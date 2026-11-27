"""Run the selected authorized Gazebo 9 graph-state application and birth path."""
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
    base=base.replace('#define GZ_PROFILE', 'namespace msgs {struct SerializedState;}\n#define GZ_PROFILE')
    base=base.replace('static std::ostringstream gzwarn;', 'static std::ostringstream gzwarn,gzerr;')
    base=base.replace('#include <unordered_map>', '#include <unordered_map>\n#include <unordered_set>')
    base=base.replace('struct BaseComponent {','struct BaseComponent {\n  void Deserialize(std::istream&){assert(false);}')
    base=base.replace('struct EntityComponentManagerDiff', """namespace components {
    struct Factory {
      static Factory* Instance(){static Factory f;return &f;}
      bool HasType(int)const{return false;}
      std::unique_ptr<BaseComponent> New(int)const{assert(false);return {};}
    };
}
struct EntityComponentManagerDiff""")
    base=base.replace('void RemoveEntity(Entity){assert(false);}', 'void RemoveEntity(Entity){assert(false);}\n void ResetNewEntityState(){assert(false);}')
    base=base.replace('  void ProcessRemoveEntityRequests();', """  void ProcessRemoveEntityRequests();
  void ClearNewlyCreatedEntities();
  void SetState(const msgs::SerializedState&);
  void RemoveComponent(Entity,ComponentTypeId){assert(false);}
""")
    base=base.replace('void RequestRemoveEntity(Entity e,bool recurse)', 'void RequestRemoveEntity(Entity e,bool recurse=false)')
    base=base.replace('  const components::BaseComponent* ComponentImplementation','  components::BaseComponent* ComponentImplementation')
    base=base.replace('  void CreateComponentImplementation(Entity,ComponentTypeId,const components::BaseComponent*){assert(false);}', '  bool CreateComponentImplementation(Entity,ComponentTypeId,const components::BaseComponent*){assert(false);return false;}')
    base=base.replace('  std::set<Entity> createdCompTypes','  void AddModifiedComponent(Entity){assert(false);}\n  std::set<Entity> createdCompTypes')
    methods.extend(['void EntityComponentManager::ClearNewlyCreatedEntities()', 'void EntityComponentManager::SetState(\n    const msgs::SerializedState &_stateMsg)'])
    pinned='\n'.join(extract(ecm,f) for f in methods[0:-1])
    state=extract(ecm,methods[-1])
    base=base.replace('/*PINNED*/',pinned)

    assert 'this->initialEntityCompMgr.CopyFrom(this->entityCompMgr);' in run
    loop=run[run.index('    this->UpdateCurrentInfo();'):]
    cut=extract(loop,'    if (this->resetInitiated)\n    {','\n    }')
    special=extract(run[run.index('void SimulationRunner::UpdateSystems()'):],
                    '  if (this->resetInitiated)\n  {','\n  }')
    step=extract(run,'void SimulationRunner::Step(')
    assert step.index('this->PublishStats();')<step.index('this->UpdateSystems();')<step.index('this->ProcessMessages();')
    d=(HERE/'runner.inc').read_text().split('enum class Op',1)[0]
    d=d.replace('bool has_state()const{return false;} // declared service without state injection',"""std::optional<SerializedState> desired;
 const SerializedState& state()const{return desired.value();}
 bool has_state()const{return desired.has_value();}""")
    d=d.replace('namespace msgs {','namespace msgs {\n/*MESSAGES*/')
    d=d.replace(' void ProcessMessages();',' void ProcessMessages();\n void ProcessNewWorldControlState();')
    d=d.replace('/*RUNNER_CODE*/','/*RUNNER_CODE*/\n/*STATE_CODE*/')
    rmethods.append('void SimulationRunner::ProcessNewWorldControlState()')
    assert step.index('this->ProcessNewWorldControlState();')<step.index('this->PublishStats();')
    clear=step.index('this->entityCompMgr.ClearNewlyCreatedEntities();')
    assert step.index('this->ProcessMessages();')<clear<step.index('this->entityCompMgr.ProcessRemoveEntityRequests();')
    cases=(HERE/'state_cases.inc').read_text()
    d=d.replace('/*MESSAGES*/',cases.split('/*TEST BODY*/')[0])
    d=d.replace('/*STATE_CODE*/',state)
    d+=cases.split('/*TEST BODY*/')[1]
    for key,text in dict(CONTROL=extract(header,"struct WorldControl","\n    };"),ECM_CUT=cut,SYSTEM_CUT=special,RUNNER_CODE='\n'.join(extract(run,f) for f in rmethods)).items():
        assert d.count('/*'+key+'*/')==1,key
        d=d.replace('/*'+key+'*/',text)
    with tempfile.TemporaryDirectory() as t:
        c=Path(t)/'runner.cc';c.write_text(base+'\n'+d)
        exe=Path(t)/'probe'
        subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',c,'-o',exe],check=True)
        subprocess.run([exe],check=True)
if __name__=='__main__':main()
