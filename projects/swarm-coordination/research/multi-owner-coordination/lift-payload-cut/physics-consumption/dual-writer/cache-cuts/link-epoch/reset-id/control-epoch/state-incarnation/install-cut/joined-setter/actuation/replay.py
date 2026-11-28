#!/usr/bin/env python3
"""Compile selected pinned bodies in a serial ECS fixture, not a Gazebo build."""
import hashlib, subprocess, sys, tempfile
from pathlib import Path

here=Path(__file__).resolve().parent
up=Path(sys.argv[1])
def checked(name,sha):
    data=(up/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==sha,name
    return data.decode()
def grab(s,start,end):
    i=s.index(start)
    return s[i:s.index(end,i)+len(end)]
lift=checked('lift.cpp','790e4896b8543d8e7772b2af1d11ebc1bfb5caa5')
ecm=checked('EntityComponentManager.cc','53dc541a8c04170d569c06e128540d20145758b4')
assert 'componentsMarkedAsRemoved[_entity].insert(_typeId)' in ecm
assert 'auto comp = this->ComponentImplementation(_entity, _typeId);' in ecm
assert 'if (!this->dataPtr->ComponentMarkedAsRemoved(_entity, _type))' in ecm
p8=checked('Physics8.cc','a5df3d7d5d5c52de93d3f7cd2c272fc79d961bd8')
p9=checked('Physics9.cc','9207f9d48a8b725293fb6e276a2b899ae6de4240')
for p in (p8,p9):
    f=grab(p,'void Physics::Update(', '\n}')
    assert f.index('UpdatePhysics(_ecm)')<f.index('Step(_info.dt)')<f.index('UpdateSim(_ecm')
get=grab(lift,'std::vector<Entity> get_payloads(','\n  }').replace('get_payloads(','Lift::get_payloads(',1)
body=lift.split('// Move payloads as well\n',1)[1].split('\n          }',1)[0]
def accept(v,p):
    return f'void Physics::consume{v}(ECS& _ecm){{\n'+grab(
        p,'_ecm.Each<components::Model, components::LinearVelocityCmd>(', '\n      });')+'\n}'
clean8=grab(p8,'_ecm.Each<components::LinearVelocityCmd>(', '\n      });')
clean9=grab(p9,'std::vector<Entity> entitiesLinearVelocityCmd;', '\n    }\n  }').removesuffix('\n  }')
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    s=d/'probe.cc'
    s.write_text('\n'.join([(here/'fixture.inc').read_text(),get,
        'void Lift::write(ECS& ecm,const Entity& entity,double target_velocity){'+body+'\n}',
        accept(8,p8),accept(9,p9),
        'void cleanup8(ECS& _ecm){'+clean8+'\n}',
        'void cleanup9(ECS& _ecm){'+clean9+'\n}',(here/'traces.inc').read_text()]))
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',s,'-o',d/'probe'],check=True)
    subprocess.run([d/'probe'],check=True)
