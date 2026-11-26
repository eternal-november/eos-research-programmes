from hashlib import sha1
from pathlib import Path
import sys
here=Path(__file__).resolve().parent
base=Path(sys.argv[1])
for row in (here/"SOURCE.tsv").read_text().splitlines():
    name,repo,rev,source,sha=row.split("\t")
    b=(base/name).read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha,name
