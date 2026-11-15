# Erdős Problem 97 · The eleven-vertex case

**An end-to-end Lean 4 verification in discrete geometry**

Dang Khoa Nguyen · [ORCID 0009-0005-3242-0098](https://orcid.org/0009-0005-3242-0098)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23923795.svg)](https://doi.org/10.5281/zenodo.23923795)

[Read the preprint](paper/Erdos97_Paper.pdf) · [Inspect the Lean theorem](erdos97_mathlib/EndToEnd_Closed_V38.lean) · [Download the archived evidence](https://zenodo.org/records/23923795)

For any eleven planar points in strictly convex counterclockwise order, some vertex has at most three other vertices at any fixed distance from it. In a hypothetical counterexample, each vertex would have four equidistant neighbours, possibly at a different radius for each vertex. The Lean theorem covers exactly eleven vertices under `StrictCCW11`.

| Verification | Result |
| --- | --- |
| Final declaration | `T34Closed.erdos97_n11_strict_ccw` |
| Exhaustive cases | 210 root cases with verified branch coverage |
| Clean replay | 680 project modules compiled from pinned inputs |
| Axioms reported for the final theorem | `propext`, `Classical.choice`, `Quot.sound` |

## How the proof works

1. **Reduce to finite choices.** Select four witnesses per vertex in a hypothetical counterexample and encode each selection as a row of a finite table.
2. **Rule out impossible choices.** Use geometric lemmas to justify pruning and strict quadrilateral inequalities to derive contradictions from equalities of edge lengths.
3. **Verify complete coverage.** Check every retained child of each search branch in Lean. The final theorem combines the certified tables with all 210 root cases. The certificate producer is outside the proof's trusted base.

The [final Lean log](verification/audit/EndToEnd_Closed_V38.log) records the declaration and its axioms. The [preprint](paper/Erdos97_Paper.pdf) explains the geometric lemmas, the certificate checker and the limits of the computation.

## Repository contents

| Path | Contents |
| --- | --- |
| [`erdos97_mathlib/`](erdos97_mathlib/) | Frozen Lean project sources and pinned toolchain and dependency files |
| [`auxiliary/`](auxiliary/) | Two supplementary Lean developments outside the final theorem's dependency chain |
| [`paper/`](paper/) | Preprint PDF and LaTeX source |
| [`verification/`](verification/) | Offline audit tools and selected records from the completed replay |
| [`BUILD_PLAN.json`](BUILD_PLAN.json) | Compilation order used for the clean replay |
| [`SOURCE_MANIFEST.json`](SOURCE_MANIFEST.json) | Inventory of the complete frozen input bundle |

## Inspect or verify the artifacts

The [Zenodo release](https://doi.org/10.5281/zenodo.23923795) contains `Erdos97_Proof_Evidence.zip` (9.98 GB). It includes the frozen certificate data, compiled proof objects, receipts and logs. To check the archive locally, place it outside the Git checkout and run the following with Python 3.10 or later:

```shell
python verification/verify_release.py --archive "path/to/Erdos97_Proof_Evidence.zip" --quick
```

Both `--quick` and `--full` stream the archive. Full mode also checks member SHA-256 digests, CRCs and the nested frozen inputs. These commands audit stored artifacts and records. A source replay requires Lean and runs separately.

To reproduce compilation, extract `CLEAN_INPUT_V41.zip` from the evidence ZIP, use the pinned Lean 4.36.0-rc1 toolchain and mathlib revision, and mount the certificate tokens at `/persistent/root_tokens_v33` in the Linux environment used for the build. Follow the frozen build order and the reproduction appendix in the preprint. The replay can require substantial CPU time and memory. The [environment record](verification/audit/FINAL_ENVIRONMENT_V59.json) lists the exact dependency revisions.

## Citation and licenses

Dang Khoa Nguyen. *An End-to-End Lean Verification of the Eleven-Vertex Case of Erdős Problem 97*. Preprint and research artifacts, v1.0.0, 2026. [DOI 10.5281/zenodo.23923795](https://doi.org/10.5281/zenodo.23923795).

Author-owned program source is available under the [MIT License](LICENSE). The author-owned manuscript, documentation and research data use CC BY 4.0. See [LICENSES.md](LICENSES.md) for scope and upstream rights.
