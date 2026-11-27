"""Prepare one development replay using only hash-pinned source inputs."""
import argparse
from hashlib import sha1
from pathlib import Path
from urllib.request import urlopen
p=argparse.ArgumentParser()
p.add_argument("part",choices=("cops","radio"))
p.add_argument("--offline",action="store_true",help="only check local inputs")
a=p.parse_args()
root=Path(__file__).resolve().parent/a.part
for line in (root/"INPUTS.tsv").read_text().splitlines():
    local,repo,ref,remote,want=line.split("\t")
    dst=root/local
    if dst.is_file():
        data=dst.read_bytes()
    else:
        if a.offline:raise FileNotFoundError(dst)
        with urlopen(f"https://raw.githubusercontent.com/{repo}/{ref}/{remote}",timeout=25) as r:
            data=r.read()
    got=sha1(f"blob {len(data)}\0".encode()+data).hexdigest()
    if got!=want:raise ValueError((local,want,got))
    if not dst.exists():
        dst.parent.mkdir(parents=True,exist_ok=True)
        dst.write_bytes(data)
