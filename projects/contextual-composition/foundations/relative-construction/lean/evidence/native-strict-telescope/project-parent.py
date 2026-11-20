"""Copy just the manifest-listed bytes from the native merged Lean subtree into a fresh directory."""
from pathlib import Path
import sys,json,hashlib,shutil
m,p,o=map(Path,sys.argv[1:]); assert not o.exists(); rows=json.loads(m.read_bytes()); assert len(rows)==490 and hashlib.sha256(m.read_bytes()).hexdigest()=="e94f897ea9fcc98534d40fbd0bce1cdc8c38f3fea73a57291af0e57e77d526c8"
for k,h in rows.items():
 s=(p/k).read_bytes(); assert hashlib.sha256(s).hexdigest()==h,k
 d=o/k;d.parent.mkdir(exist_ok=True,parents=True);d.write_bytes(s)
