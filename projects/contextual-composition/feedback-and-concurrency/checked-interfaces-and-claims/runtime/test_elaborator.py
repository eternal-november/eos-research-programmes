from test_checker import I,S,W,O,P
from checker import Checker
from elaborator import Elaborated
from ordered_runtime import leaves
E=Elaborated(Checker(I,S,W,O,P))
for raw in (0,1):
 m=E.start('main','x',('z','a'),0,{'z':0,'a':0})
 while m.jobs[0].mode!='done':
  pid=m.phase_next();m.step(pid,outcome=raw);m.assert_invariant()
  for result_pid,j in m.jobs.items():
   if j.result and not j.claimed:
    for leaf in leaves(j.result.tree):
     tag,value=leaf.value
     assert value in I[tag]['values']
     assert tuple(m.kinds[c] for c in leaf.caps)==I[tag]['kinds']
 assert [leaf.caps for leaf in leaves(m.jobs[0].result.tree)]==[('z',),('a',)]
 assert m.weight==(1 if raw==0 else 0)
loop=E.start('loop','same',('z',),0,{'z':0}).prefix(50)
assert loop.jobs[0].mode=='eval' and not loop.events
print('PASS: checked table elaboration per-step frontier/result typing, zero-weight branches, unbounded recursive prefix')

# Caller and intermediary declaration mutation cannot rewrite the compiled snapshot.
from copy import deepcopy
i,o,p=deepcopy(I),deepcopy(O),deepcopy(P)
checked=Checker(i,S,W,o,p)
e=Elaborated(checked)
p['main']['body']={'op':'call','name':'missing'}
o['split']['table'].clear()
checked.P['main']['input']='empty'
checked.O['split']['table'].clear()
m=e.start('main','x',('z','a'),0,{'z':0,'a':0}).prefix(50,stop_at_root=True)
assert m.jobs[0].mode=='done' and len(leaves(m.jobs[0].result.tree))==2
print('PASS: original and checked intermediary mutation does not change compiled program')

# A claimed historical result is provenance, not live typing against changed kinds.
from fractions import Fraction as F
I2={'pair':{'kinds':('K','K'),'values':('x',)},'post':{'kinds':('L',),'values':('y',)}}
S2={'K':(0,),'L':(1,)}
r={'weight':F(1),'cost':[0],'world':0,'consume':['0'],'retype':{'1':'L'},'stores':{'1':1},'tree':{'tag':'post','value':'y','slots':['1']}}
O2={'change':{'input':'pair','output':['post'],'table':{('x',0,(0,0)):[[r]]}}}
P2={'main':{'input':'pair','output':['post'],'body':{'op':'bind','left':{'op':'ret'},'handlers':{('pair','x'):{'op':'primitive','name':'change'}}}}}
m=Elaborated(Checker(I2,S2,(0,),O2,P2)).start('main','x',('z','a'),0,{'z':0,'a':0})
while m.jobs[0].mode!='done':
 m.step(m.phase_next());m.assert_invariant()
 for pid,j in m.jobs.items():
  if j.result and not j.claimed:
   for leaf in leaves(j.result.tree):
    tag,value=leaf.value
    assert tuple(m.kinds[c] for c in leaf.caps)==I2[tag]['kinds']
    assert all(m.ledger[c]==('result',pid) for c in leaf.caps)
assert m.ledger['z']==('retired','z') and m.kinds['a']=='L' and m.stores['a']==1
assert m.jobs[1].claimed and m.jobs[1].result.tree.caps==('z','a')
print('PASS: consumption/retyping changes live frontier without retyping historical provenance')

# None is a legitimate finite world, not an omitted constructor argument.
IN={'e':{'kinds':(),'values':('x',)}}
RN={'weight':F(1),'cost':[0],'world':None,'stores':{},'tree':{'tag':'e','value':'x','slots':[]}}
ON={'n':{'input':'e','output':['e'],'table':{('x',None,()):[[RN]]}}}
PN={'n':{'input':'e','output':['e'],'body':{'op':'primitive','name':'n'}}}
CN=Checker(IN,{},(None,),ON,PN)
n=Elaborated(CN).start('n','x',(),None,{})
assert n.world is None
n.prefix(20,stop_at_root=True)
assert n.jobs[0].mode=='done' and n.world is None
print('PASS: explicit None world survives ordinary checked entry and primitive lookup')
