"""Selected pinned entity allocator/diff/reset, not a simulator run."""
from pathlib import Path
import hashlib
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PINS={
    "EntityComponentManager.cc":"53dc541a8c04170d569c06e128540d20145758b4",
    "SimulationRunner.cc":"bc51fde1f428c7a03bf8c803ccec60e88b01aefc",
}
def verify(p):
    r=p.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(r)).encode()+b'\0'+r).hexdigest()==PINS[p.name]
    return r.decode()
def extract(d,a,b='\n}'):
    i=d.index(a)
    return d[i:d.index(b,i)+len(b)]
def main():
    u=Path(sys.argv[1])
    e,s=(verify(u/k) for k in PINS)
    assert 'this->initialEntityCompMgr.CopyFrom(this->entityCompMgr);' in s
    k=s.index('this->entityCompMgr.ResetTo(this->initialEntityCompMgr);')
    assert k<s.index('this->Step(this->currentInfo);',k)
    parts=['void EntityComponentManagerPrivate::CopyFrom(',
     'Entity EntityComponentManager::CreateEntity()',
     'Entity EntityComponentManagerPrivate::CreateEntityImplementation(',
     'void EntityComponentManager::ProcessRemoveEntityRequests()',
     'void EntityComponentManager::CopyFrom(',
     'EntityComponentManagerDiff EntityComponentManager::ComputeEntityDiff(',
     'void EntityComponentManager::ApplyEntityDiff(',
     'void EntityComponentManager::ResetTo(']
    code=(HERE/'fixture.cc').read_text().replace('/*PINNED*/','\n'.join(extract(e,b) for b in parts))
    with tempfile.TemporaryDirectory() as t:
        f=Path(t)/'fixture.cc';f.write_text(code)
        o=Path(t)/'probe'
        subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',f,'-o',o],check=True)
        subprocess.run([o],check=True)
if __name__=='__main__':main()
