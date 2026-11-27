"""Execute pinned Gazebo link source bodies with a serial entity/engine fixture."""
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path

HERE=Path(__file__).resolve().parent
PINS={
    'VelocityControl.cc':'7af66e743b17415aba8ff3bf60567e8682541ab8',
    'Physics9.cc':'9207f9d48a8b725293fb6e276a2b899ae6de4240',
    'ECM-detail.hh':'423cd229a51616b3a6f8e4e74c4ea7218cc16342',
    'EntityComponentManager.cc':'53dc541a8c04170d569c06e128540d20145758b4',
    'Model.cc':'1dda31dc0d459896ae13f83c52a2fb1155dd4c70',
    'Util.cc':'4ff805e9dd70d777ba8893ea01df477b01d28e8b',
}
def get(folder,name,sha):
    b=(folder/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha,name
    return b.decode()
def grab(doc,a,b='\n}'):
    p=doc.index(a);q=doc.index(b,p)
    return doc[p:q+len(b)]
def main():
    pins=Path(sys.argv[1]).resolve()
    p={f:get(pins,f,h) for f,h in PINS.items()}
    v,c,f,e,m,u=(p[k] for k in PINS)
    assert 'if (!this->HasEntity(_entity))' in e.split('bool EntityComponentManager::CreateComponentImplementation(',1)[1].split('if (!this->HasComponentType',1)[0]
    assert 'this->dataPtr->UpdateLinkVelocity(_info, _ecm);' in v
    pre=grab(v,'void VelocityControl::PreUpdate(')
    latches='\n'.join(grab(v,'void VelocityControlPrivate::'+x+'(') for x in ('UpdateLinkVelocity','OnLinkCmdVel'))
    comp=grab(f,'template<typename ComponentTypeT>\nbool EntityComponentManager::SetComponentData(')
    pmodel=grab(c,'_ecm.Each<components::Model, components::LinearVelocityCmd>(', '\n      });')
    plink=grab(c,'_ecm.Each<components::Link, components::LinearVelocityCmd>(', '\n      });')
    rel=grab(c,'math::Pose3d PhysicsPrivate::RelativePose(')
    top=grab(u,'sim::Entity topLevelModel(').replace('sim::Entity','Entity',1)
    model=grab(m,'Entity Model::LinkByName(')
    fixture=(HERE/'fixture.cc').read_text()
    for name,body in dict(S=comp,M=model,T=top,R=rel,P=pre,L=latches,C=pmodel+'\n'+plink).items():
        assert fixture.count('/*'+name+'*/')==1,name
        fixture=fixture.replace('/*'+name+'*/',body)
    fixture=fixture.replace('/*TESTS*/',(HERE/'scenarios.inc').read_text())
    with tempfile.TemporaryDirectory() as d:
        cc=Path(d)/'p.cc';cc.write_text(fixture)
        exe=Path(d)/'replay'
        subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',cc,'-o',exe],check=True)
        subprocess.run([exe],check=True)
if __name__=='__main__':main()
