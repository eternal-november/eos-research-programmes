import re
from pathlib import Path
from hashlib import sha1
from subprocess import run
from tempfile import TemporaryDirectory
p=Path(__file__).parent.resolve()
s={}
for ln in (p/'PINS.tsv').read_text().splitlines():
    n,_,_,_,h=ln.split('\t')
    f=(p/n).read_bytes()
    assert sha1(f'blob {len(f)}\0'.encode()+f).hexdigest()==h,n
    s[n]=f.decode()
def cut(file,name,endindent=''):
    c=s[file]
    a=c.index(name)
    a=c.rfind('\n',0,a)+1
    b=c.index('\n'+endindent+'}',a)+len(endindent)+2
    return c[a:b]
base=cut('classic_sensor.cc','void Sensor::Update(const bool')
assert base.index('this->UpdateImpl(_force)')<base.index('this->updated();')
assert 'ConnectUpdated' in s['ariac_camera.cpp']
camera=[cut('classic_camera.cc',n) for n in
        ('bool LogicalCameraSensor::UpdateImpl','bool LogicalCameraSensor::IsActive','msgs::LogicalCameraImage LogicalCameraSensor::Image')]
wrap=[cut('ariac_camera.cpp',n) for n in
      ('void AriacLogicalCameraPluginPrivate::OnUpdate()','void AriacLogicalCameraPlugin::SensorHealthCallback(')]
tm=[cut('upstream.cpp',n,'    ') for n in
    ('void TaskManagerPluginPrivate::AGV1TraySensorCallback','void TaskManagerPlugin::OnAGV1StatusCallback','void TaskManagerPluginPrivate::GetPreAssemblyPoses')]
assert not re.search(r'\b(?:stamp|generation|header|time)\b',s['logical_camera_image.proto']+s['pose.proto'])
with TemporaryDirectory() as tmp:
    d=Path(tmp)
    (d/'selected.inc').write_text('\n'.join(camera+wrap+tm))
    (d/'replay.cpp').write_bytes((p/'replay.cpp').read_bytes())
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-Wno-sign-compare','replay.cpp','-o','replay'],cwd=d,check=True)
    run([d/'replay'],cwd=d,check=True)
