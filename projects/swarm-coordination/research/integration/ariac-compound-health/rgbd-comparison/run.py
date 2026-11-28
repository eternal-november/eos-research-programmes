from pathlib import Path
from hashlib import sha1
from tempfile import TemporaryDirectory
from subprocess import run
import sys
root=Path(__file__).resolve().parent
n='upstream.cpp'
b=(root/n).read_bytes()
assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()=="9fcc58712dec0ef2a7af7df36095a9296031902e"
s=b.decode()
def extract(k):
    i=s.index(k)
    return s[i:s.index('\n}',i)+2]
names=['void AriacCameraPlugin::OnNewDepthFrame(', 'void AriacCameraPlugin::SensorHealthCallback(']
with TemporaryDirectory() as tmp:
    p=Path(tmp)
    (p/'selected.inc').write_text('\n'.join(extract(n) for n in names))
    (p/'replay.cpp').write_bytes((root/'replay.cpp').read_bytes())
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-Wno-unused-parameter','replay.cpp','-o','replay'],cwd=p,check=True)
    r=run([p/'replay'],input=sys.stdin.read(),check=True,capture_output=True,text=True)
    print(r.stdout,end='')
