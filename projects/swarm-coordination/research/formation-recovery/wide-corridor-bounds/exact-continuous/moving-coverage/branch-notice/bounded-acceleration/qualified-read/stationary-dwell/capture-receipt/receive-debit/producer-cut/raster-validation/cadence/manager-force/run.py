from pathlib import Path
from hashlib import sha1
from tempfile import TemporaryDirectory
from subprocess import run
root=Path(__file__).resolve().parent
c={}
for line in (root/'INPUTS.tsv').read_text().splitlines():
    name,_,_,_,h=line.split('\t')
    b=(root/name).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
    c[name]=b.decode()
def extract(s,a):
    i=s.index(a);return s[i:s.index('\n}',i)+2]
code=[extract(c['Sensor.cc'],'bool Sensor::Update(const gz::common::Time &_now,'),
      extract(c['Manager.cc'],'Sensor *Manager::Sensor(').replace('Sensor *Manager','::Sensor *Manager',1),
      extract(c['Manager.cc'],'void Manager::RunOnce(')]
with TemporaryDirectory() as d:
    d=Path(d);(d/'selected.inc').write_text('\n'.join(code))
    (d/'dispatch.cc').write_bytes((root/'dispatch.cc').read_bytes())
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','dispatch.cc','-o','replay'],cwd=d,check=True)
    run([d/'replay'],cwd=d,check=True)
