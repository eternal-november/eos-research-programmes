#!/usr/bin/env python3
"""Verify review bytes and optionally the separate exact source archives; no theorem execution."""
from pathlib import Path
import argparse,hashlib,json,sys,zipfile
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(x,message):
    if not x:raise RuntimeError(message)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archives',type=Path,help='Directory containing all 21 separately delivered source archives');args=ap.parse_args()
    manifest=json.loads((HERE/'PUBLIC_FILE_MANIFEST.json').read_text())
    for row in manifest['files']:
        p=HERE/row['member'];require(p.is_file(),'Missing review file '+row['member']);require(sha(p)==row['sha256'],'Changed review file '+row['member'])
    out={'status':'PASS','review_files':len(manifest['files']),'scope':'Artifact integrity only; no mathematical replay or acceptance promotion'}
    if args.archives:
        loc=json.loads((HERE/'archive_member_locator_index.json').read_text());count=0
        expected={}
        for h,rows in loc['members_by_sha256'].items():
            for r in rows:expected.setdefault(r['archive_filename'],{})[r['member']]=h
        for row in loc['archives']:
            p=args.archives/row['filename'];require(p.is_file(),'Missing source archive '+row['filename']);require(sha(p)==row['sha256'],'Changed source archive '+row['filename'])
            with zipfile.ZipFile(p) as z:
                for member,h in expected[row['filename']].items():require(hashlib.sha256(z.read(member)).hexdigest()==h,'Member hash mismatch '+member);count+=1
        out.update(source_archives=len(loc['archives']),source_archive_members=count)
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
