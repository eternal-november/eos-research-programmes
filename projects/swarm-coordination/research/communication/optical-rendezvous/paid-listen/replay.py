from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction
from hashlib import sha1
from itertools import combinations, product
from pathlib import Path
import io
import json
from hashlib import sha256

with redirect_stdout(io.StringIO()):
    import optical_source as model
raw=Path(model.__file__).read_bytes()
assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='b71839d2ec757e4826266466f12072f647070233'

def complete(blocked, listen, first, frozen=None, decoded=None):
    # Controller after its policy chose the branch: inspect the incident
    # corridor, reverse on a closed edge, and physically exchange the
    # retained report. The source still controls legality and custody.
    w=(blocked,True)
    good=5-blocked
    state=model.INIT
    depart=3 if listen else 2
    assert first in model.available(w,model.HUB)
    trace=()
    for t in range(15):
        x,y,_,custody,_,_=state
        if t<2:a=model.WAIT
        elif t==2:a=model.BEACON
        elif t==3:a=good
        elif x==y and custody==0:a=model.GIVE
        elif custody>0 and x==good:a=model.REFUGE
        else:a=model.WAIT
        if t==0:b=model.BASE
        elif t==1:b=model.HUB
        elif t==2 and listen:b=model.LISTEN
        elif t==depart:b=first
        elif custody==0 and y in (2,3) and model.REFUGE not in model.available(w,y):b=model.HUB
        elif custody==0 and y==model.HUB and t>depart:b=5-first
        elif custody==0 and x==y:b=model.TAKE
        elif custody==1 and y!=model.HUB:b=model.HUB
        elif custody==1:b=model.BASE
        else:b=model.WAIT
        if frozen is not None:
            trace+=(model.view(w,state,1),)
            b=frozen[trace]
            trace+=((b,),)
        assert a in model.possible(w,state,0,True) and b in model.possible(w,state,1,True)
        state=model.step(w,state,a,b,t)
        assert state is not None and state[4]
        if frozen is not None and t==2:
            # The adapter translates a certified opposite-branch decision
            # into the frozen receiver's canonical no-pulse/pulse values.
            state=state[:-1]+(0 if decoded==2 else 3,)
        if state[0]==model.REFUGE and state[1]==model.BASE and state[3]==2:
            return t+1

routes={(w,listen,first):complete(w,listen,first) for w,listen,first in
        product((2,3),(False,True),(2,3))}
assert all(t==(7 if b!=k else 9 if listen else 8) for (b,listen,k),t in routes.items())

def exact(support,force=None):
    result=[]
    for _,left,right in support:
        options=[]
        for listen in (False,True):
            if force is not None and listen!=force:continue
            observations=sorted(set(left)|set(right)) if listen else [None]
            for assignment in product((2,3),repeat=len(observations)):
                local=dict(zip(observations,assignment))
                times=[routes[(w,listen,local[r if listen else None])]
                       for w,rs in zip((2,3),(left,right)) for r in rs]
                options.append(max(times))
        result.append(min(options))
    return max(result)

def check(config):
    overlap=any(set(l)&set(r) for _,l,r in config)
    for force in (None,True,False):
        predicted=(9 if overlap else 7) if force is True else (8 if overlap or force is False else 7)
        for H in range(6,10):
            assert (exact(config,force)<=H)==(H>=predicted),(config,force,H,predicted)
    return 12

possible=(0,model.LEFT,model.RIGHT)
subsets=[xs for n in range(1,len(possible)+1) for xs in combinations(possible,n)]
checks=sum(check(((0,a,b),)) for a,b in product(subsets,repeat=2))
configs=[
    ((0,(0,),(3,)), (1,(0,2),(0,3))),
    ((0,(2,),(3,)), (1,(3,),(2,))),
]
for config in configs: checks+=check(config)
print(f'route replay/complete first-choice search: {checks} deadline cases; all 49 support pairs; two regime-code variants')
policy_bytes=Path(__file__).with_name('receiver_policy.json').read_bytes()
assert sha256(policy_bytes).hexdigest()=='208fc5f93de281dea7568f48cada4fefd9e1fcd8d26b679500ca3251399cbfaa'
def frozen_tuple(x):return tuple(map(frozen_tuple,x)) if isinstance(x,list) else x
policy=dict(frozen_tuple(json.loads(policy_bytes)))
assert len(policy)==11
adapter_checks=0
for a,b in product(subsets,repeat=2):
    if set(a)&set(b):continue
    for branch,support in zip((2,3),(a,b)):
        for output in support:
            candidates=[i for i,opts in zip((2,3),(a,b)) if output in opts]
            assert candidates==[branch]
            assert complete(branch,True,5-candidates[0],policy,candidates[0])==7
            adapter_checks+=1
print(f'byte-identical receiver table: {adapter_checks} finite translations on certified disjoint supports')

# Two equally weighted branches and four bits per attempted packet. The
# first bit is the prescribed branch decision; non-branch errors are not
# confused with a successful application packet. This is an authored
# metric-identifiability fixture, not replay of an acoustic device.
# Rows: probability, erasure flag, number of wrong bits after decode.
one_sided=(
    [(Fraction(1,2),True,4),(Fraction(1,2),False,0)],
    [(Fraction(1),False,2)],
)
shared=tuple([(Fraction(1,4),True,4),(Fraction(1,2),False,1),(Fraction(1,4),False,2)] for _ in range(2))
def counts(ch):
    t=tuple(sum(p*k/4 for p,_,k in branch) for branch in ch)
    e=sum(p for branch in ch for p,l,_ in branch if l)/2
    return t,e
assert counts(one_sided)==counts(shared)==((Fraction(1,2),)*2,Fraction(1,4))
assert {i for i,b in enumerate(one_sided) if any(ell for _,ell,_ in b)}=={0}
assert {i for i,b in enumerate(shared) if any(ell for _,ell,_ in b)}=={0,1}
print('equal aggregate erasure=1/4 and per-branch TER=1/2; absence names a branch in only one law')
