"""Drive exact pinned selected Gazebo and Open-RMF replay without source edits."""
from pathlib import Path
import subprocess,sys,tempfile
here=Path(__file__).resolve().parent
up=Path(sys.argv[1]).resolve()
s=(up/'cache.inc').read_text()
assert s.count('\nint main(){')==1
fixture=s.split('\nint main(){')[0]+'\n'+(here/'cases.inc').read_text()
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    (d/'cache.inc').write_text(fixture)
    (d/'replay.py').write_bytes((up/'cache.py').read_bytes())
    subprocess.run([sys.executable,'-B',d/'replay.py',up,up/'base'],check=True)
