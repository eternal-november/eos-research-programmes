from typed_admin import *
from fractions import Fraction as F
I={'in':{'kinds':('K',),'values':('x',)},'out':{'kinds':('K',),'values':('same',)},'empty':{'kinds':(),'values':('same',)}}
O={'split':{'input':'in','output':['out','empty'],'table':{('x',0,(0,)):[[
 {'weight':F(1),'cost':[0],'world':0,'stores':{'0':0},'tree':{'node':'branch','children':[{'tag':'out','value':'same','slots':['0']},{'tag':'empty','value':'same','slots':[]}]}}
 ]]}}}
P={'child':{'input':'in','output':['out','empty'],'body':{'op':'primitive','name':'split'}}}
core=Checker(I,{'K':(0,)},(0,),O,P)
channels={'q':{'Q':['out','empty'],'kinds':[]}}
creator=[{'op':'spawn','child':'child','value':'x','slots':['s0'],'handle':'a','ticket':'ta'},
 {'op':'send','channel':'q','handle':'a','ticket':'ta','slots':[]},{'op':'return'}]
receiver=[{'op':'receive','channel':'q','handle':'fresh_local','ticket':'r','slots':[]},{'op':'await','ticket':'r'}]
a=Admin(core,channels,('K',),creator);b=Admin(core,channels,(),receiver)
program=Batch(lambda v,cs:((a.term(),None,cs),(b.term(),None,())))
m=ClaimMachine(program,caps=('work',),kinds={'work':'K'},stores={'work':0},world=0,primitives=a.core.primitives,procedures=a.core.procedures).prefix(100,stop_at_root=True)
assert m.jobs[0].mode=='done'
assert len(m.claim_rights)==1 and all(m.ledger[c][0]=='retired' for c in m.claim_rights)
assert len([x for x in m.trace if x[0]=='claim-await'])==1
assert m.ledger['work']==('result',0)
assert len(leaves(m.jobs[0].result.tree))==4 # sender return, two child holes, receiver reserve
print('PASS: checked child Q, existential queue renaming, multi-hole terminal await and reserve')

def bad(script,initial=('K',),ch=channels):
 try:Admin(core,ch,initial,script)
 except (Rejected,KeyError):return
 raise AssertionError('invalid admin script accepted')
x=deepcopy(creator);x[0]['Q']=['in'];bad(x)
x=deepcopy(creator);x[0]['value']='bad';bad(x)
x=[deepcopy(creator[0]),dict(deepcopy(creator[0]),slots=['s1'],handle='b',ticket='tb'),dict(deepcopy(creator[1]),handle='b'),{'op':'return'}];bad(x,('K','K'))
x=deepcopy(creator);x[-1]={'op':'await','ticket':'ta'};bad(x)
x=deepcopy(receiver);x.insert(1,dict(x[0],ticket='r2'));bad(x,())
x=deepcopy(creator);bad(x,ch={'q':{'Q':['out','empty'],'kinds':['K']}})
print('PASS: forged Q/input, cross-target pairing, used ticket, binder capture and package kinds rejected')

network=start_network([a,b],[('work',),()],{'work':0},0).prefix(100,stop_at_root=True)
assert network.jobs[0].mode=='done'
# Sender keeps copy a; receiving under fresh binder b may denote SAME actual child.
alias_script=[deepcopy(creator[0]),deepcopy(creator[1]),dict(deepcopy(receiver[0]),handle='b'),{'op':'await','ticket':'r'}]
alias=Admin(core,channels,('K',),alias_script)
n=start_network([alias],[('work',)],{'work':0},0).prefix(100,stop_at_root=True)
assert n.jobs[0].mode=='done' and len(n.claim_rights)==1
print('PASS: closed checked network; fresh logical receive binder may alias retained handle')

x=deepcopy(creator);x[0]['handle']=123;bad(x)
x=deepcopy(receiver);x[0]['handle']=123;bad(x,())
# Compile/start before mutation; all lazy continuations use a frozen checked snapshot.
a0=Admin(core,channels,('K',),creator);b0=Admin(core,channels,(),receiver)
net=start_network([a0,b0],[('work',),()],{'work':0},0)
a0.script[0]['child']='missing';a0.plans[0]['indices']=(999,)
b0.script[-1]['ticket']='missing';b0.channels.clear()
net.prefix(100,stop_at_root=True)
assert net.jobs[0].mode=='done' and len(net.claim_rights)==1
# Direct term() also ignores corrupted cached plans and freezes all lazy script tails.
a1=Admin(core,channels,('K',),creator);a1.plans[0]['indices']=(999,)
frozen=a1.term();a1.script.clear();a1.plans.clear()
direct=ClaimMachine(frozen,caps=('work',),kinds={'work':'K'},stores={'work':0},world=0,primitives=core and a1.core.primitives,procedures=a1.core.procedures).prefix(100,stop_at_root=True)
assert direct.jobs[0].mode=='done' and direct.queues['q']
print('PASS: non-string binders rejected; source/cache mutation cannot change started or compiled scripts')
# Check the actual existential package and child result invariant at every prefix.
a2=Admin(core,channels,('K',),creator);b2=Admin(core,channels,(),receiver)
net=start_network([a2,b2],[('work',),()],{'work':0},0)
seen_message=seen_finished_child=False
while net.jobs[0].mode!='done':
 net.step(net.phase_next())
 for channel,mids in net.queues.items():
  schema=channels[channel]
  for mid in mids:
   seen_message=True
   caps=net.owned(('msg',mid));_,package=net.messages[mid]
   assert caps and caps[0] in net.claim_rights
   target,q=net.claim_rights[caps[0]]
   assert package.handle==target and q==repr(tuple(sorted(schema['Q'])))
   assert tuple(net.kinds[c] for c in caps[1:])==tuple(schema['kinds'])
   assert set(caps)=={c for c,loc in net.ledger.items() if loc==('msg',mid)}
 for ticket,(target,q) in net.claim_rights.items():
  child=net.jobs[target]
  if child.mode=='done':
   seen_finished_child=True
   for leaf in leaves(child.result.tree):
    tag,value=leaf.value
    assert tag in channels['q']['Q'] and value in core.I[tag]['values']
    assert tuple(net.kinds[c] for c in leaf.caps)==tuple(core.I[tag]['kinds'])
assert seen_message and seen_finished_child
print('PASS: every-prefix existential queue linkage, ordered escrow schema and checked child return bound')

reserved=Checker(I,{'K':(0,),ClaimMachine.JOIN:(0,)},(0,),O,P)
try:Admin(reserved,channels,('K',),creator)
except Rejected:pass
else:raise AssertionError('reserved protected kind admitted as ordinary signature')
print('PASS: reserved protected kind rejected even when not initially held')

# The inherited adapter must preserve None at the closed-network entry too.
from fractions import Fraction as F
NI={'e':{'kinds':(),'values':('x',)}}
NR={'weight':F(1),'cost':[0],'world':None,'stores':{},'tree':{'tag':'e','value':'x','slots':[]}}
NO={'n':{'input':'e','output':['e'],'table':{('x',None,()):[[NR]]}}}
NP={'n':{'input':'e','output':['e'],'body':{'op':'primitive','name':'n'}}}
nc=Checker(NI,{},(None,),NO,NP)
na=Admin(nc,{},(),[{'op':'spawn','child':'n','slots':[],'value':'x','handle':'h','ticket':'t'},{'op':'await','ticket':'t'}])
nm=start_network([na],[()],{},None)
assert nm.world is None
nm.prefix(80,stop_at_root=True)
assert nm.jobs[0].mode=='done' and nm.world is None
print('PASS: explicit None world survives checked closed-network entry and child execution')
