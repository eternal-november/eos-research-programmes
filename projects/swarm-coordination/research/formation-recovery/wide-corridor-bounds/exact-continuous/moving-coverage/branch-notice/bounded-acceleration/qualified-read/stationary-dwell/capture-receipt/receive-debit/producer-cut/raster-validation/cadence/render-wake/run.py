from pathlib import Path
from hashlib import sha1
from subprocess import run
from tempfile import TemporaryDirectory
root=Path(__file__).resolve().parent
pins={}
for line in (root/'INPUTS.tsv').read_text().splitlines():
    name,_,_,_,h=line.split('\t')
    b=(root/name).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h, name
    pins[name]=b.decode()
assert 'ignition-sensors3' in pins['CMakeLists.txt'] and 'VERSION 3.3' in pins['CMakeLists.txt']
def take(name,begin):
    s=pins[name]
    i=s.index(begin)
    return s[i:s.index('\n}',i)+2]
pieces=[
    take('Sensor.cc','bool Sensor::Update(const gz::common::Time &_now,'),
    take('Sensor.cc','gz::common::Time Sensor::NextUpdateTime() const'),
    take('Manager.cc','Sensor *Manager::Sensor(').replace('Sensor *Manager','::Sensor *Manager',1),
    take('Manager.cc','void Manager::RunOnce('),
    take('Sensors.cc','void Sensors::PostUpdate('),
    take('Sensors.cc','void SensorsPrivate::RunOnce()')]
with TemporaryDirectory() as tmp:
    d=Path(tmp)
    (d/'selected.inc').write_text('\n'.join(pieces))
    (d/'replay.cc').write_bytes((root/'replay.cc').read_bytes())
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-pthread','replay.cc','-o','replay'],cwd=d,check=True)
    r=run([d/'replay'],cwd=d,check=True,capture_output=True,text=True)
    print(r.stdout,end='')
    if (root/'expected.txt').exists():
        assert r.stdout==(root/'expected.txt').read_text()
