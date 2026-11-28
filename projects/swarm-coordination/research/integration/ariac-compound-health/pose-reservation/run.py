import re
from pathlib import Path
from hashlib import sha1
from tempfile import TemporaryDirectory
from subprocess import run
root=Path(__file__).resolve().parent
for line in (root/'INPUTS.tsv').read_text().splitlines():
    name,_,_,_,h=line.split('\t')
    v=(root/name).read_bytes()
    assert sha1(f'blob {len(v)}\0'.encode()+v).hexdigest()==h,name
b=(root/'upstream.cpp').read_bytes()
s=b.decode()
def cut(name):
    m=re.search(r'^    void\s+'+name+r'\(',s,re.M)
    assert m is not None,name
    return s[m.start():s.index('\n    }',m.end())+6]
names=['TaskManagerPluginPrivate::AGV1TraySensorCallback',
       'TaskManagerPlugin::OnAGV1StatusCallback','TaskManagerPluginPrivate::GetPreAssemblyPoses']
with TemporaryDirectory() as tmp:
    t=Path(tmp)
    (t/'replay.cpp').write_bytes((root/'replay.cpp').read_bytes())
    (t/'selected.inc').write_text('\n'.join(cut(n) for n in names))
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-Wno-sign-compare','replay.cpp','-o','replay'],cwd=t,check=True)
    run([t/'replay'],cwd=t,check=True)
