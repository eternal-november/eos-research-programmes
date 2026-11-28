import subprocess
import sys
from itertools import product
from prior_core import Event, Row, Use, check

# This lowering is for admission at one owned cut. A synthetic paid
# key represents an accepted local outcome; it is not mission delivery.
local_return=('effect-cut-response',)
bank=('named-same-cut-physical-resource',)
cases=0
for act_class,*bits in product(('inspect','effect'),*[range(2)]*4):
    scope,value,room,ready=bits
    args=[sys.argv[1],act_class,*map(str,bits)]
    outcome=int(subprocess.check_output(args, text=True))
    facts=frozenset(k for k,b in zip(('scope','value','service'),(scope,value,ready)) if b)
    inspect=act_class=='inspect'
    need=frozenset(('scope','value')) if inspect else frozenset(('scope','value','service'))
    new_uses=() if inspect else (Use(bank,1,1,1),)
    prior=() if room else (Event(0,0,uses=(Use(bank,1,1,1),)),)
    row=Row((),facts,prior,{'request':(Event(1,1,need=need,uses=new_uses,paid=(local_return,)),)})
    accepted=check(row,'request',1,{local_return:1})
    assert accepted == (outcome==(0 if inspect else 6))
    cases+=1
print(f"single-cut projections matching prior prefix core {cases}")
