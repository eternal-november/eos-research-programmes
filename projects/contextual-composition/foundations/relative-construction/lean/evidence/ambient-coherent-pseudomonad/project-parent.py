"""Copy just the manifest-listed bytes from the native merged Lean subtree into a fresh directory."""
from pathlib import Path
import sys,json,hashlib,shutil
m,p,o=map(Path,sys.argv[1:]); assert not o.exists(); rows=json.loads(m.read_bytes()); assert len(rows)==295 and hashlib.sha256(m.read_bytes()).hexdigest()=="9e93c35a700fa403d4e40465f3f430ab09b3d6ab9eec77576d77202447ade586"
for k,h in rows.items():
 s=(p/k).read_bytes(); assert hashlib.sha256(s).hexdigest()==h,k
 d=o/k;d.parent.mkdir(exist_ok=True,parents=True);d.write_bytes(s)
