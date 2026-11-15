#!/usr/bin/env python3
"""Read-only, standard-library verifier for the frozen Erdős #97 n=11 evidence ZIP.

No Modal, Lean, shell commands, network requests, or extraction are performed.
All byte-level tests are enforced through exceptions, even when Python uses -O.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
import re
import sys
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = {
    "T34Closed.all_roots",
    "T34Closed.no_counterexample",
    "T34Closed.erdos97_n11_strict_ccw",
}
FINAL = "EndToEnd_Closed_V38"
CHUNK = 8 * 1024 * 1024

class VerificationError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def read_json_path(path):
    with Path(path).open("r", encoding="utf-8-sig") as fp:
        return json.load(fp)

def read_json_zip(z, name):
    try:
        return json.loads(z.read(name))
    except (KeyError, ValueError, UnicodeDecodeError) as exc:
        raise VerificationError(f"Cannot read {name}: {exc}") from exc

def sha256_path(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as fp:
        for b in iter(lambda: fp.read(CHUNK), b""):
            h.update(b)
    return h.hexdigest()

def digest_member(z, name, expected_size, expected_sha256):
    h = hashlib.sha256()
    total = 0
    try:
        with z.open(name, "r") as fp:
            while chunk := fp.read(CHUNK):
                h.update(chunk)
                total += len(chunk)
    except (OSError, ValueError, RuntimeError, zipfile.BadZipFile) as exc:
        raise VerificationError(f"Cannot decompress {name}: {exc}") from exc
    require(total == expected_size, f"Size mismatch: {name}: {total} != {expected_size}")
    require(h.hexdigest() == expected_sha256, f"SHA-256 mismatch: {name}")
    # zipfile checks stored CRC when decompression reaches end of file.
    return total

def verify_zip(archive, mode):
    release = read_json_path(HERE / "RELEASE_MANIFEST.json")
    expected = release["evidence"]
    require(archive.is_file(), f"Evidence ZIP not found: {archive}")
    size = archive.stat().st_size
    require(size == expected["bytes"], f"Evidence size mismatch: {size} != {expected['bytes']}")
    print(f"[1/5] Evidence ZIP: {archive.name} ({size:,} bytes)", flush=True)
    actual_zip_sha = sha256_path(archive)
    require(actual_zip_sha == expected["sha256"],
            f"Evidence ZIP SHA-256 mismatch: {actual_zip_sha}")
    print(f"[2/5] Whole-ZIP SHA-256 PASS: {actual_zip_sha}", flush=True)

    with zipfile.ZipFile(archive, "r", allowZip64=True) as z:
        names = z.namelist()
        require(len(names) == len(set(names)), "Duplicate ZIP member names")
        for n in names:
            p = Path(n)
            require(not p.is_absolute() and '..' not in p.parts and '\\' not in n,
                    f"Suspicious ZIP member path: {n!r}")
        inv = read_json_zip(z, "FILES_SHA256_V59.json")
        require(set(names) == set(inv) | {"FILES_SHA256_V59.json"},
                "Members differ from FILES_SHA256_V59.json inventory")
        for name, info in inv.items():
            require(isinstance(info.get("bytes"), int) and info["bytes"] >= 0,
                    f"Invalid inventory size: {name}")
            require(re.fullmatch(r"[0-9a-f]{64}", info.get("sha256", "")) is not None,
                    f"Invalid inventory digest: {name}")
            require(z.getinfo(name).file_size == info["bytes"],
                    f"ZIP header size does not match inventory: {name}")

        manifest = read_json_zip(z, "CLEAN_REPLAY_FINAL_MANIFEST_V59.json")
        source = read_json_zip(z, "SOURCE_MANIFEST.json")
        plan = read_json_zip(z, "BUILD_PLAN.json")
        receipt = manifest.get("verified_modules", {})
        module_list = plan.get("topological_modules", [])
        dependencies = plan.get("dependencies", {})
        require(manifest.get("run_id") == "clean41-20261025" and
                manifest.get("scope") == "n=11 StrictCCW11", "Wrong run/scope")
        require(manifest.get("verified_module_count") == 680 and len(receipt) == 680,
                "Incomplete number of verified modules")
        require(len(module_list) == 680 and len(set(module_list)) == 680 and
                set(module_list) == set(receipt) == set(dependencies),
                "Build plan / receipt module set mismatch")
        require(manifest.get("clean_rebuild_complete") is True and
                manifest.get("final_kernel_pass") is True and
                manifest.get("all_project_objects_created_in_clean41_run") is True and
                manifest.get("original_V38_objects_imported") is False and
                not manifest.get("pending_modules"), "Completion flags are inconsistent")
        require(manifest.get("clean_input_zip_sha256") == release["clean_input"]["sha256"] ==
                inv["CLEAN_INPUT_V41.zip"]["sha256"], "Source ZIP hash mismatch")
        require(manifest.get("pinned_lean_commit") == release["toolchain"]["lean_commit"] and
                manifest.get("pinned_mathlib") == release["toolchain"]["mathlib_commit"],
                "Toolchain pins mismatch")

        for prefix, extension in (("objects/", ".olean"),
                                  ("records/", ".json"), ("logs/", ".log")):
            got = {n[len(prefix):-len(extension)] for n in names
                   if n.startswith(prefix) and n.endswith(extension)}
            require(got == set(receipt), f"Missing/extra {prefix} members")

        order = {n: i for i, n in enumerate(module_list)}
        edges = 0
        for module in module_list:
            for dep in dependencies[module]:
                edges += 1
                require(dep in order and order[dep] < order[module],
                        f"Dependency not in topological order: {module} -> {dep}")

        # Independently rebuild each module's transitive import closure from the plan.
        closures = {}
        for module in module_list:
            seen, todo = set(), list(dependencies[module])
            while todo:
                dep = todo.pop()
                if dep not in seen:
                    seen.add(dep)
                    todo.extend(dependencies[dep])
            closures[module] = seen
            r = receipt[module]
            require(r.get("module") == module and r.get("run_id") == "clean41-20261025",
                    f"Incorrect receipt identity: {module}")
            require(r.get("kernel_pass") is True and r.get("exit_code") == 0 and
                    r.get("source_compiled_this_run") is True and
                    not r.get("interrupted", False) and not r.get("budget_stop", False),
                    f"Unsuccessful recorded compilation: {module}")
            s = source.get(f"erdos97_mathlib/{module}.lean")
            require(s is not None and s["sha256"] == r.get("source_sha256"),
                    f"Source hash conflict: {module}")
            require(inv[f"objects/{module}.olean"]["sha256"] == r.get("olean_sha256"),
                    f"Compiled object hash conflict: {module}")
            required_deps = r.get("fresh_dependency_objects", {})
            require(set(required_deps) == seen, f"Transitive closure mismatch: {module}")
            for dep in seen:
                require(required_deps[dep].get("source_sha256") == receipt[dep]["source_sha256"] and
                        required_deps[dep].get("olean_sha256") == receipt[dep]["olean_sha256"],
                        f"Dependency hash conflict: {module} -> {dep}")

        roots = [n for n in dependencies[FINAL] if re.match(r"^Root_\d{3}_", n)]
        require(len(roots) == 210 and {int(n.split('_')[1]) for n in roots} == set(range(210)),
                "Final theorem does not import precisely 210 roots")
        require(closures[FINAL] == set(receipt) - {FINAL},
                "Final theorem does not cover all other 679 modules")
        final = receipt[FINAL]
        require(manifest.get("final_result") == final, "Final result differs from receipt")
        ax = final.get("final_axioms", {})
        require(set(ax) == THEOREMS and all(set(v) == AXIOMS for v in ax.values()),
                "Final theorem axiom report mismatch")
        log = z.read(f"logs/{FINAL}.log").decode("utf-8", errors="replace")
        require("sorryAx" not in log, "sorryAx appears in final log")
        for theorem in THEOREMS:
            require(f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,
                    f"Final log lacks expected axiom output: {theorem}")
        for item in ("CLEAN_REPLAY_FINAL_MANIFEST_V59.json", "FILES_SHA256_V59.json",
                     "SOURCE_MANIFEST.json", "BUILD_PLAN.json", "EndToEnd_Closed_V38.json"):
            # EndToEnd_Closed_V38.json lives inside records/, not at archive root.
            if item == "EndToEnd_Closed_V38.json":
                continue
            public = HERE / "audit" / item
            if public.is_file():
                require(read_json_path(public) == (inv if item == "FILES_SHA256_V59.json" else
                        manifest if item == "CLEAN_REPLAY_FINAL_MANIFEST_V59.json" else
                        source if item == "SOURCE_MANIFEST.json" else plan),
                        f"Public audit metadata differs: {item}")
        print(f"[3/5] Manifests/closure PASS: 680 modules, 210 roots, {edges:,} direct imports", flush=True)

        if mode == "full":
            print(f"[4/5] Hashing/decompressing {len(inv):,} inventory members (may be I/O-intensive)...", flush=True)
            for i, (name, info) in enumerate(inv.items(), start=1):
                digest_member(z, name, info["bytes"], info["sha256"])
                if i % 250 == 0:
                    print(f"  {i:,}/{len(inv):,} members verified", flush=True)
            require(read_json_zip(z, f"records/{FINAL}.json") == final,
                    "Final member receipt differs from canonical manifest")
            for module in module_list:
                require(read_json_zip(z, f"records/{module}.json") == receipt[module],
                        f"Receipt member differs: {module}")
                require(b"sorryAx" not in z.read(f"logs/{module}.log"),
                        f"sorryAx in module log: {module}")
            # Nested source ZIP: verify every input file including the token payload.
            with zipfile.ZipFile(io.BytesIO(z.read("CLEAN_INPUT_V41.zip"))) as nested:
                source_items = set(source)
                require(source_items <= set(nested.namelist()), "Frozen source file missing")
                for name, meta in source.items():
                    digest_member(nested, name, meta["bytes"], meta["sha256"])
            print("[5/5] Full member SHA/CRC, receipts and 899 frozen inputs PASS", flush=True)
        else:
            print("[4/5] Per-member data rehash skipped (--full enables it)", flush=True)
            print("[5/5] QUICK checks PASS; this is metadata + whole-archive integrity", flush=True)

    return dict(status="PASS", mode=mode, archive_sha256=actual_zip_sha,
                modules=680, roots=210, scope="n=11 StrictCCW11")

def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--archive", type=Path, help="Path to complete proof-evidence ZIP (any filename)")
    g = p.add_mutually_exclusive_group()
    g.add_argument("--quick", dest="mode", action="store_const", const="quick",
                   help="Verify complete ZIP SHA-256, metadata, closure and final log (default)")
    g.add_argument("--full", dest="mode", action="store_const", const="full",
                   help="Also decompress/hash every archived file and all nested source inputs")
    p.add_argument("--report", type=Path, help="Optional path for a local report JSON")
    args = p.parse_args(argv)
    mode = args.mode or "quick"
    candidates = [Path.cwd() / "Erdos97_Proof_Evidence.zip",
                  Path.cwd() / "Erdos97_Clean_Replay_FULL680_V59_20261102.zip"]
    archive = args.archive or next((x for x in candidates if x.is_file()), None)
    if archive is None:
        p.error("Specify --archive PATH (evidence ZIP may have any filename)")
    try:
        result = verify_zip(archive, mode)
    except (VerificationError, OSError, zipfile.BadZipFile, KeyError, TypeError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    if args.report:
        args.report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("PASS — inspection only; this does not independently run Lean.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
