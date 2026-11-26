#!/usr/bin/env python3
"""Add a pinned producer and the native set-or-create seam to the prior fixture."""
import hashlib,subprocess,sys,tempfile
from pathlib import Path
here=Path(__file__).resolve().parent
up=Path(sys.argv[1]).resolve()
parent=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else here.parent
def pin(name,sha):
    d=(up/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()==sha,name
    return d.decode()
def grab(s,a,b):
    i=s.index(a)
    return s[i:s.index(b,i)+len(b)]
v=pin('VelocityControl.cc','7af66e743b17415aba8ff3bf60567e8682541ab8')
e=pin('ECM-detail.hh','423cd229a51616b3a6f8e4e74c4ea7218cc16342')
r=pin('SimulationRunner.cc','bc51fde1f428c7a03bf8c803ccec60e88b01aefc')
s=pin('SystemManager.cc','dcb24902c10a4211d81b8c8494c7a23141e43d0c')
pr=r.index('for (auto& [priority, systems] : this->systemMgr->SystemsPreUpdate())')
assert pr<r.index('for (auto& [priority, systems] : this->systemMgr->SystemsUpdate())')
assert 'systemsPreupdate[p].push_back(system.preupdate)' in s
assert 'system.configureSdf->Get<PriorityType>' in s
write=grab(v,'_ecm.SetComponentData<components::LinearVelocityCmd>(',');')
change=grab(e,'template<typename ComponentTypeT>\nbool EntityComponentManager::SetComponentData(', '\n}')
change=change.replace('EntityComponentManager::SetComponentData','ECS::SetComponentData')
fixture=(parent/'fixture.inc').read_text()
def inject(old,new):
    global fixture
    assert fixture.count(old)==1,old
    fixture=fixture.replace(old,new)
inject('math::Vector3d v{};','''using Type=math::Vector3d;
  math::Vector3d v{};
  template<class F> bool SetData(const Type& d,F different){
    if(different(v,d))return false;
    v=d;
    return true;
  }''')
inject('else return &commands.at(e);','''else { auto c=commands.find(e); return c==commands.end()?nullptr:&c->second; }''')
inject('  bool EntityHasComponentType(','''  template<class T> bool SetComponentData(Entity,const typename T::Type&);
  template<class T> void CreateComponent(Entity e,T d){assert(!commands.contains(e));commands.emplace(e,d);}
  bool EntityHasComponentType(''')
driver=(here/'order.inc').read_text()
driver=driver.replace('/*SET_BODY*/',change).replace('/*PRODUCER_BODY*/',write)
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    (d/'replay.py').write_bytes((parent/'replay.py').read_bytes())
    (d/'fixture.inc').write_text(fixture)
    (d/'traces.inc').write_text(driver)
    subprocess.run([sys.executable,'-B',d/'replay.py',up],check=True)
