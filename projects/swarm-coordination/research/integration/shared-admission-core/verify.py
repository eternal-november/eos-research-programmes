from hashlib import sha1
from pathlib import Path
import sys
here=Path(__file__).resolve().parent
locations=dict(zip(('SP','NAMED','FLIGHT','RF'),map(Path,sys.argv[1:]),strict=True))
for row in (here/'COMPONENTS.tsv').read_text().splitlines():
    key,rev,name,sha=row.split('\t')
    b=(locations[key]/name).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==sha,(key,name,rev)
