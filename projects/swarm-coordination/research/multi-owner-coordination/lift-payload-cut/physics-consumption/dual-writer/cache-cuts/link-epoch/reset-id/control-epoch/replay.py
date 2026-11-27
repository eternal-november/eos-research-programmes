"""Run selected Gazebo 9 control, clock, runner-cut and entity-reset source."""
from pathlib import Path
import hashlib
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
SOURCES={
    'EntityComponentManager.cc':'53dc541a8c04170d569c06e128540d20145758b4',
    'SimulationRunner.cc':'bc51fde1f428c7a03bf8c803ccec60e88b01aefc',
    'WorldControl.hh':'9eaf267a691edf61a4dc765b5bac1883e1a64c66',
}
def read(root,name,h):
    b=(root/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h
    return b.decode()
def extract(s,begin,end='\n}'):
    i=s.index(begin)
    return s[i:s.index(end,i)+len(end)]
def main():
    p=Path(sys.argv[1]);ecm,run,header=(read(p,n,h) for n,h in SOURCES.items())
    methods=['void EntityComponentManagerPrivate::CopyFrom(',
             'Entity EntityComponentManager::CreateEntity()',
             'Entity EntityComponentManagerPrivate::CreateEntityImplementation(',
             'void EntityComponentManager::ProcessRemoveEntityRequests()',
             'void EntityComponentManager::CopyFrom(',
             'EntityComponentManagerDiff EntityComponentManager::ComputeEntityDiff(',
             'void EntityComponentManager::ApplyEntityDiff(',
             'void EntityComponentManager::ResetTo(']
    rmethods=['void SimulationRunner::SetRunToSimTime(',
              'bool SimulationRunner::OnWorldControl(',
              'bool SimulationRunner::OnWorldControlState(',
              'bool SimulationRunner::OnPlaybackControl(',
              'void SimulationRunner::ProcessMessages()',
              'void SimulationRunner::ProcessWorldControl()',
              'void SimulationRunner::UpdateCurrentInfo()']
    base=(HERE/'base.inc').read_text().split('struct Report {',1)[0]
    base=base.replace('/*PINNED*/','\n'.join(extract(ecm,f) for f in methods))
    assert 'this->initialEntityCompMgr.CopyFrom(this->entityCompMgr);' in run
    loop=run[run.index('    this->UpdateCurrentInfo();'):]
    cut=extract(loop,'    if (this->resetInitiated)\n    {','\n    }')
    special=extract(run[run.index('void SimulationRunner::UpdateSystems()'):],
                    '  if (this->resetInitiated)\n  {','\n  }')
    step=extract(run,'void SimulationRunner::Step(')
    assert step.index('this->PublishStats();')<step.index('this->UpdateSystems();')<step.index('this->ProcessMessages();')
    d=(HERE/'runner.inc').read_text()
    for key,text in dict(CONTROL=extract(header,"struct WorldControl","\n    };"),ECM_CUT=cut,SYSTEM_CUT=special,RUNNER_CODE='\n'.join(extract(run,f) for f in rmethods)).items():
        assert d.count('/*'+key+'*/')==1,key
        d=d.replace('/*'+key+'*/',text)
    with tempfile.TemporaryDirectory() as t:
        c=Path(t)/'runner.cc';c.write_text(base+'\n'+d)
        exe=Path(t)/'probe'
        subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',c,'-o',exe],check=True)
        subprocess.run([exe],check=True)
if __name__=='__main__':main()
