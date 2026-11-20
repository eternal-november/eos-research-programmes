"""Copy just the manifest-listed bytes from the native merged Lean subtree into a fresh directory."""
from pathlib import Path
import sys,json,hashlib,shutil
m,p,o=map(Path,sys.argv[1:]); assert not o.exists(); rows=json.loads(m.read_bytes()); assert len(rows)==259
for k,h in rows.items():
 s=(p/k).read_bytes(); assert hashlib.sha256(s).hexdigest()==h,k
 d=o/k;d.parent.mkdir(exist_ok=True,parents=True);d.write_bytes(s)
