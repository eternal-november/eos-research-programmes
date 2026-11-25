from pathlib import Path
import hashlib,sys
root=Path(sys.argv[1])
for line in Path(__file__).with_name("SOURCE.tsv").read_text().splitlines():
    n,repo,commit,path,sha=line.split("\t")
    data=(root/n).read_bytes()
    assert hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==sha,n
