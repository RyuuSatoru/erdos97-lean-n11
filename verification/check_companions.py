"""Check manuscript source ZIP and separately distributed PDF, without external dependencies."""
from pathlib import Path
import argparse, hashlib, json, sys, zipfile, re

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(8*1024*1024),b''):
            h.update(block)
    return h.hexdigest()

def check(paths):
    here=Path(__file__).resolve().parent
    entry=json.loads((here/'RELEASE_MANIFEST.json').read_text(encoding='utf-8'))['manuscript']
    pdf=Path(paths.paper); pkg=Path(paths.manuscript)
    for file, expected, expected_size in [(pdf,entry['paper_sha256'],entry['paper_bytes']),(pkg,entry['sha256'],entry['bytes'])]:
        if not file.is_file():raise ValueError(f'File missing: {file}')
        if file.stat().st_size != expected_size:raise ValueError(f'Wrong file size: {file}')
        if sha(file) != expected:raise ValueError(f'SHA-256 mismatch: {file}')
    with zipfile.ZipFile(pkg) as z:
        names=z.namelist()
        if len(names)!=len(set(names)):
            raise ValueError('Duplicate ZIP member names')
        for n in names:
            pn=Path(n)
            if pn.is_absolute() or '..' in pn.parts or '\\' in n:
                raise ValueError(f'Unsafe ZIP member path: {n}')
        if z.testzip() is not None:
            raise ValueError('ZIP CRC verification failed')
        actual=z.read(entry['paper_name'])
        if hashlib.sha256(actual).hexdigest()!=entry['paper_sha256'] or actual!=pdf.read_bytes():
            raise ValueError('PDF inside manuscript ZIP differs from standalone PDF')
        if 'SHA256SUMS.txt' not in names:
            raise ValueError('Internal SHA256SUMS.txt missing')
        verified=set()
        for line in z.read('SHA256SUMS.txt').decode('utf-8').splitlines():
            if not line.strip():
                continue
            match=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
            if not match:
                raise ValueError('Malformed SHA256SUMS.txt line')
            expected, member=match.groups()
            if member in verified or member not in names:
                raise ValueError(f'Duplicate or missing internal member: {member}')
            verified.add(member)
            if hashlib.sha256(z.read(member)).hexdigest()!=expected:
                raise ValueError(f'SHA-256 mismatch inside ZIP: {member}')
        required={entry['paper_name'],'source/article.tex','source/main.tex','source/references.bib'}
        if not required.issubset(verified):
            raise ValueError('Required manuscript sources not covered by SHA256SUMS.txt')
    print('PASS: source ZIP, internal source checksums, standalone PDF, and embedded PDF match the release manifest')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manuscript',required=True,help='Path to Erdos97_Manuscript_Source.zip')
    ap.add_argument('--paper',required=True,help='Path to Erdos97_Paper.pdf')
    args=ap.parse_args()
    try:check(args)
    except (OSError, ValueError, KeyError, zipfile.BadZipFile) as exc:
        print(f'FAIL: {exc}',file=sys.stderr);return 1
    return 0
if __name__=='__main__':sys.exit(main())
