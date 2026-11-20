"""Copy just the manifest-listed bytes from the native merged Lean subtree into a fresh directory."""
from pathlib import Path
import sys,json,hashlib,shutil
m,p,o=map(Path,sys.argv[1:]); assert not o.exists(); rows=json.loads(m.read_bytes()); assert len(rows)==468 and hashlib.sha256(m.read_bytes()).hexdigest()=="7539d8afa5e0bfdb39dcf8b1717b7fe76d988492ff1fe30bb4b230d0f6b301dd"
for k,h in rows.items():
 s=(p/k).read_bytes(); assert hashlib.sha256(s).hexdigest()==h,k
 d=o/k;d.parent.mkdir(exist_ok=True,parents=True);d.write_bytes(s)
