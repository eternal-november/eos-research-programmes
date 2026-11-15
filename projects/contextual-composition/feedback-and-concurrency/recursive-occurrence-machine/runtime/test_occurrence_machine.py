from fractions import Fraction as F
from itertools import product
from copy import deepcopy
from occurrence_machine import *
from legacy_oracle import evaluate


def sample_table(arg,caps,world,stores):
    assert len(caps)==2
    tree=Node('split',(Leaf('same',(caps[0],)),Leaf('same',(caps[1],))))
    return ((Outcome('positive',F(1),(1,),'split',tree,world),
             Outcome('zero',F(0),(7,),'split',tree,world)),)

def unary(name,weights=(F(1),)):
    def table(arg,caps,world,stores):
        return (tuple(Outcome(name+str(i),w,(2,),name,Node(name,(Leaf(arg,caps),)),world,
                              stores={c:stores.get(c,0)+1 for c in caps}) for i,w in enumerate(weights)),)
    return table

primitives={'split':sample_table,'q':unary('q',(F(1,2),F(1,2))),'r':unary('r')}
term=Bind(Bind(Op('split'),lambda x:Op('q')),lambda x:Op('r'))
for choices in product(range(2),repeat=3):
    cursor=iter(choices)
    def choose(name):return (0,next(cursor)) if name in ('split','q') else (0,0)
    oracle=evaluate(term,None,('a','b'),primitives,choose,stores={'a':0,'b':10})
    m=Machine(term,caps=('a','b'),stores={'a':0,'b':10},primitives=primitives)
    cursor=iter(choices)
    for _ in range(200):
        if m.jobs[0].mode=='done':break
        pid=m.phase_next();j=m.jobs[pid]
        oi=next(cursor) if j.mode=='eval' and isinstance(j.term,Op) and j.term.name in ('split','q') else 0
        m.step(pid,outcome=oi)
    assert m.jobs[0].mode=='done'
    r=m.jobs[0].result
    assert (r.tree,r.raw,m.weight,m.cost,m.word,m.world,m.stores)==(oracle.tree,oracle.raw,oracle.weight,oracle.cost,oracle.word,oracle.world,oracle.stores)
    assert m.word==('split','q','q','r','r')
    assert m.weight==(F(0) if choices[0] else F(1,4))
    assert len(leaves(r.tree))==2
    assert m.owned(('result',0))==('a','b')
print('PASS: 8 phase-oracle branches, exact raw/tree/store/weight/cost/word including zero weight')

other=Bind(Op('split'),lambda x:Bind(Op('q'),lambda y:Op('r')))
a=Machine(term,caps=('a','b'),primitives=primitives).prefix(200,stop_at_root=True)
b=Machine(other,caps=('a','b'),primitives=primitives).prefix(200,stop_at_root=True)
assert a.jobs[0].result.tree==b.jobs[0].result.tree
assert a.word!=b.word and b.word==('split','q','r','q','r')
print('PASS: bind bracketings retain equal causal tree but distinct phase chronology')

# Nullary return tree consumes only explicitly declared authority; no phantom child.
def stop(arg,caps,w,s):return ((Outcome('stop',F(1),(3,),'stop',Node('stop',()),w,consume=caps),),)
n=Machine(Bind(Op('stop'),lambda x:(_ for _ in ()).throw(AssertionError('phantom continuation'))),caps=('a',),primitives={'stop':stop}).prefix(50,stop_at_root=True)
assert n.jobs[0].mode=='done' and leaves(n.jobs[0].result.tree)==[] and n.ledger['a']==('retired','a')
print('PASS: nullary hole product, declared retirement, no phantom continuation')

# Structural batch adds no physical event; split ownership prevents sibling-store exposure.
seen=[]
def inspect(arg,caps,w,s):
    seen.append(set(s));return ((Outcome('only',F(1),(0,),'inspect',Leaf(arg,caps),w),),)
bat=Batch(lambda v,cs:((Op('inspect'),1,(cs[0],)),(Op('inspect'),2,(cs[1],))))
bm=Machine(bat,caps=('a','b'),stores={'a':'private-A','b':'private-B'},primitives={'inspect':inspect}).prefix(100,stop_at_root=True)
assert seen==[{'a'},{'b'}] and bm.word==('inspect','inspect') and bm.jobs[0].result.tree.structural
print('PASS: separated batch and private-store boundary')

# Actual shared-state interleaving: both jobs cache 0 then write 1 => lost update.
def read(arg,caps,w,s):return ((Outcome('read',F(1),(0,),'read',Leaf(w['count'],caps),w),),)
def write(arg,caps,w,s):w['count']=arg+1;return ((Outcome('write',F(1),(0,),'write',Leaf(arg+1,caps),w),),)
inc=Bind(Op('read'),lambda x:Op('write'))
race=Machine(Batch(lambda v,cs:((inc,None,()),(inc,None,()))),world={'count':0},primitives={'read':read,'write':write})
race.step(0) # batch children1,2
race.step(1);race.step(2) # left read jobs3,4
race.step(3);race.step(4) # both snapshots
race.prefix(100,stop_at_root=True)
serial=Machine(Batch(lambda v,cs:((inc,None,()),(inc,None,()))),world={'count':0},primitives={'read':read,'write':write}).prefix(100,stop_at_root=True)
assert race.world['count']==1 and serial.world['count']==2
print('PASS: genuine interference distinguishes concurrent schedule from serial phase schedule')

# Revalidation refuses stale evidence without erasing pending reservation.
def reserve(arg,caps,w,s):
    w['pending'].append('ticket');return ((Outcome('reserved',F(1),(0,),'reserve',Leaf(w['version'],caps),w),),)
def validate(arg,caps,w,s):
    answer='committed' if arg==w['version'] else 'refused-stale'
    if answer=='committed':w['committed']+=1;w['pending'].remove('ticket')
    return ((Outcome(answer,F(1),(0,),answer,Leaf(answer,caps),w),),)
stale=Machine(Bind(Op('reserve'),lambda x:Op('validate')),caps=('permit',),world={'version':0,'pending':[],'committed':0},primitives={'reserve':reserve,'validate':validate})
stale.step();stale.step() # left completes reservation
stale.environment_step('external-change',lambda w:{**w,'version':w['version']+1})
stale.prefix(50,stop_at_root=True)
assert stale.world=={'version':1,'pending':['ticket'],'committed':0}
assert leaves(stale.jobs[0].result.tree)[0].value=='refused-stale'
assert stale.owned(('result',0))==('permit',)
print('PASS: stale revalidation refusal preserves pending effect and syntactic capability')

# Spawn -> send escrow -> receive -> await with explicit parent reserve.
child=Bind(Send('mail',lambda v,c:c,lambda v:'payload'),lambda _:Ret(lambda _: 'child-done'))
dyn=Machine(Bind(Spawn(child,lambda v,c:(c[0],)),lambda h:Bind(Receive('mail'),lambda _:Await(lambda _:h,lambda _:'parent-reserve'))),caps=('a','b'))
dyn.prefix(200,stop_at_root=True)
assert dyn.jobs[0].mode=='done' and dyn.owned(('result',0))==('a','b')
assert not dyn.messages and not dyn.queues['mail']
ls=leaves(dyn.jobs[0].result.tree)
assert [x.value for x in ls]==['child-done','parent-reserve']
assert ls[0].caps==() and ls[1].caps==('a','b')
# A separate caller with copied handle receives explicit refusal, not authority.
handle=next(pid for pid,j in dyn.jobs.items() if pid!=0 and j.parent is None)
refuser=dyn.new_job(Await(),handle,(),('job',0),(99,),None)
dyn.step(refuser)
assert leaves(dyn.jobs[refuser].result.tree)[0].value=={'refused':'unavailable result'}
print('PASS: dynamic spawn/message escrow/receive/once-only await and reserve framing')

# Multi-hole await transfers child leaves once and keeps reserve as distinct leaf.
dyn2=Machine(Bind(Spawn(Op('split'),lambda v,c:('a','b')),lambda h:Await(lambda _:h,lambda _:'reserve')),caps=('a','b','c'),primitives=primitives)
dyn2.prefix(100,stop_at_root=True)
assert [x.caps for x in leaves(dyn2.jobs[0].result.tree)]==[('a',),('b',),('c',)]
print('PASS: multi-hole await never duplicates caller reserve')

loop=Machine(Call('loop'),procedures={'loop':lambda _:Call('loop')}).prefix(100)
assert loop.jobs[0].mode=='eval' and len(loop.trace)==200 and not loop.events
blocked=Machine(Receive('never')).prefix(100)
assert blocked.jobs[0].mode=='eval' and blocked.enabled()==[]
print('PASS: unbounded-call prefix distinct from blocked receive and completed result')

# Duplicate authority is rejected; visible witness labels need not be unique.
try:
 Machine(Batch(lambda v,c:((Ret(),0,c),(Ret(),1,c))),caps=('a',)).step()
 raise AssertionError('duplicating partition accepted')
except ValueError:pass

def duplicate(arg,caps,w,s):return ((Outcome('same',F(1),(0,),'x',Leaf(None,caps),w),Outcome('same',F(0),(0,),'x',Leaf(None,caps),w)),)
d0=Machine(Op('bad'),primitives={'bad':duplicate});d0.step(outcome=0)
d1=Machine(Op('bad'),primitives={'bad':duplicate});d1.step(outcome=1)
assert d0.jobs[0].result.tree==d1.jobs[0].result.tree
assert d0.jobs[0].result.raw!=d1.jobs[0].result.raw
assert d0.weight==1 and d1.weight==0
print('PASS: malformed ownership partition rejected; equal-label raw rows remain distinct')

# A callback receives no sibling private-store entry, even when it asks explicitly.
def snoop(arg,caps,w,s):
    answer=s.get('secret','ABSENT')
    return ((Outcome('probe',F(1),(0,),'probe',Leaf(answer,caps),w),),)
isolated=Machine(Batch(lambda v,c:((Op('snoop'),None,('caller',)),(Ret(),None,('secret',)))),caps=('caller','secret'),stores={'caller':1,'secret':8675309},primitives={'snoop':snoop}).prefix(100,stop_at_root=True)
assert leaves(isolated.jobs[0].result.tree)[0].value=='ABSENT'
assert isolated.stores['secret']==8675309
print('PASS: explicit sibling-private-store read returns absent')

# Failed authority validation does not allocate or commit transaction state.
for term in (Spawn(Ret(),lambda v,c:('absent',)),Send('q',lambda v,c:('absent',))):
    m=Machine(term,caps=('a',))
    before=(deepcopy(m.jobs),dict(m.ledger),m.next_job,m.next_message,dict(m.messages),dict(m.queues))
    try:m.step();raise AssertionError('invalid transfer accepted')
    except ValueError:pass
    assert before==(m.jobs,m.ledger,m.next_job,m.next_message,m.messages,m.queues)
for weight,cost in ((.5,(0,)),(F(1),(0.5,)),(True,(0,)),(F(1),(True,))):
    def invalid(v,c,w,s):return ((Outcome('bad',weight,cost,'bad',Leaf(v,c),w),),)
    m=Machine(Op('bad'),primitives={'bad':invalid})
    try:m.step();raise AssertionError('inexact coefficient accepted')
    except ValueError:pass
    assert not m.events and m.jobs[0].mode=='eval'
entry=Machine(Call('entry',lambda v:('capture',v)),value=7,procedures={'entry':lambda pair:ProcedureEntry(Ret(),pair[1])}).prefix(3)
assert entry.jobs[0].result.tree==Leaf(7,()) and entry.jobs[0].result.raw==('ret',)
print('PASS: invalid transfers preserve allocators/state; exact coefficient validation; administrative procedure entry')

# A noninvertible strict model map forgets hidden world bit and coalesces outcomes.
def hidden_step(v,c,w,s):
    return (tuple(Outcome('hidden'+str(bit),F(1,2),(1,),'tick',Node('tick',(Leaf(v,c),)),(w[0]+1,bit)) for bit in (0,1)),)
def visible_step(v,c,w,s):
    return ((Outcome('visible',F(1),(1,),'tick',Node('tick',(Leaf(v,c),)),w+1),),)
term=Bind(Batch(lambda v,c:((Op('tick'),'x',('a',)),(Op('tick'),'x',('b',)))),lambda v:Op('tick'))
weights=[]
for bits in product((0,1),repeat=4):
    src=Machine(term,caps=('a','b'),world=(0,0),primitives={'tick':hidden_step})
    tgt=Machine(term,caps=('a','b'),world=0,primitives={'tick':visible_step})
    choices=iter(bits)
    while src.jobs[0].mode!='done':
        p=src.phase_next();assert p==tgt.phase_next()
        isop=src.jobs[p].mode=='eval' and isinstance(src.jobs[p].term,Op)
        src.step(p,outcome=next(choices) if isop else 0);tgt.step(p)
        assert src.world[0]==tgt.world and src.ledger==tgt.ledger
        assert src.next_job==tgt.next_job and src.word==tgt.word and src.cost==tgt.cost
        assert [(j.mode,j.claimed,None if j.result is None else j.result.tree) for j in src.jobs.values()]==[(j.mode,j.claimed,None if j.result is None else j.result.tree) for j in tgt.jobs.values()]
    weights.append(src.weight)
assert sum(weights)==tgt.weight==1 and len(weights)==16
print('PASS: noninvertible hidden-world projection at every prefix and exact fiber mass sum')
