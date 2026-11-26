#!/usr/bin/env python3
from pathlib import Path
import hashlib,subprocess,sys,tempfile
U=Path(sys.argv[1]); P=Path(__file__).resolve().parent
def pin(f,h):
    b=(U/f).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h,f
    return b.decode()
def snippet(s,key,tab=''):
    i=s.index(key)
    j=s.index('\n'+tab+'}',i)+len(tab)+2
    return s[i:j]
node=pin('Node.cpp','e559ba69ce580a0667c321ff8cf9725836a4ba39')
end=pin('EndLiftSession.cpp','a1c85a2eaae97573fa8c888cf0988c04d195a3c9')
sim=pin('lift.cpp','790e4896b8543d8e7772b2af1d11ebc1bfb5caa5')
# Copy the phase predicate for scope verification, not Rx execution.
assert 'state->session_id != me->_context->requester_id()' in end
with tempfile.TemporaryDirectory() as d:
    p=Path(d)
    fn='\n'.join([snippet(node,'void Node::_adapter_lift_request_update('),
                   snippet(node,'void Node::_lift_state_update(')])
    callback=sim.split('[this, ecm = &ecm](LiftRequest::UniquePtr msg)\n      {',1)[1].split('\n      });',1)[0]
    body=sim.split('// Move payloads as well\n',1)[1]
    body=body[:body.index('\n          }')]
    cc='\n'.join([(P/'standins.inc').read_text(),'namespace rmf_fleet_adapter::lift_supervisor {',fn,'}',
        snippet(sim,'std::vector<Entity> get_payloads(','  ').replace('get_payloads(','LiftPlugin::get_payloads(',1),
        snippet(sim,'LiftState get_current_state(','  ').replace('get_current_state(','LiftPlugin::get_current_state(',1),
        'void LiftPlugin::apply(EntityComponentManager* ecm,LiftRequest::UniquePtr msg){'+callback+'\n}',
        'void LiftPlugin::velocity(EntityComponentManager& ecm,const Entity& entity,double target_velocity){\n'+body+'\n}',
        (P/'tests.inc').read_text()])
    (p/'run.cc').write_text(cc)
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror','-o',p/'run',p/'run.cc'],check=True)
    subprocess.run([p/'run'],check=True)
