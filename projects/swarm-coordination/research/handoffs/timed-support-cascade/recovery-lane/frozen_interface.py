"""Finite receiver interface for the primary warehouse cascade."""
from collections import defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PRIMARY = Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parent/'swarm-c11-primary'
EXPECTED = {
    'replay.py': '88747bf5cd3e86b3ef8f1a97a5f48b7c47cff63b45309dd2507af4f5e084a1ac',
    'original.py': 'b540ced5fd26a41b287dd24e18c20fe7e53629bf061b4625f3a8ba9850397e04',
}
for n,h in EXPECTED.items():
    assert sha256((PRIMARY/n).read_bytes()).hexdigest()==h
sys.path.insert(0,str(PRIMARY))
from replay import simulate

TOKEN=(0,'maintenance-0',0)
BASES=tuple(product([1,2],[False,True],[4,5,6]))
UNDEF=('undefined',)
KINDS=('channel','support','clock')

def frames(base, variant):
    live,d,D=base
    h,early,before={'early-onset':(True,True,True),'ordinary-a':(False,False,True),
                    'ordinary-b':(False,False,False),'rejected-early':(False,True,True)}[variant]
    run=simulate(live,h,d,early,before,D)
    events=defaultdict(list)
    stock=[None]*5
    authority=None
    pending=set()
    from_local={e[0]:e[2:] for e in run['local'][1] if e[1]=='ready_check'}
    start_count=0
    previous=False
    pending_root=False
    issued=[]
    for entry in run['trace']:
        tick,kind,*p=entry
        if tick<0:
            if kind=='place_on_native_support':
                stock[p[0]]=p[0]
            if kind=='settled_on_fixed_rack':
                stock[p[0]]=None
            if kind=='send' and p[0]==0:
                issued.append(tick)
        else:
            events[tick].append((kind,p))
    rows=[]
    for t in range(D+3):
        now=events[t]
        accepts=[]
        begins=[]
        for kind,p in now:
            if kind=='send' and p[0]==0:
                issued.append(t)
            if kind=='accept':
                a,b,j=p
                assert tuple(p) in pending
                pending.remove(tuple(p))
                assert stock[a]==j and stock[b] is None
                stock[a],stock[b]=None,j
                if 1 in (a,b):
                    accepts.append(tuple(p))
            if kind=='receive' and p[0]==1:
                assert authority is None
                authority=(0,tuple(p[1]),t)
                assert t>=authority[1][2]
            if kind=='begin':
                begins.append(tuple(p))
        lock=lambda a:any(a in (i,j) for i,j,_ in pending)
        facts=stock[0],stock[1],lock(0),lock(1)
        if authority is not None:
            assert from_local[t]==list(facts)
        else:
            assert t not in from_local
        q=(*base,t)
        # Variant is retained as provenance, not exposed to the receiver.
        channel=(q,(authority,), (variant,tuple(issued)))
        support=(q,(*facts,tuple(e for e in accepts if e != (0,1,0))),variant)
        clock=(q,(t,D),variant)
        actual_start=(0,1,0) in begins
        actual_accept=(0,1,0) in accepts
        # Physical root acceptance is available exactly in the following phase.
        assert actual_accept==pending_root==previous
        start_count+=actual_start
        pending_root=actual_start
        previous=actual_start
        for g in begins:
            a,b,j=g
            assert not lock(a) and not lock(b)
            pending.add(g)
        rows.append((channel,support,clock,actual_start,actual_accept))
    assert start_count<=1 and not pending_root
    assert run['served']==any(r[-1] for r in rows if r[2][1][0]<=D)
    assert tuple(issued)==((-1,) if early else (0,))
    return rows

def token_read(w):
    return w[1][0]

def support_read(w):
    return w[1]

def clock_read(w):
    return w[1]

def match(x,y):
    # Equality of common exogenous cut and phase index is a join condition,
    # not a new observation furnished to the installed receiver.
    return x[0]==y[0]

def guard_values(c,s,k):
    auth,=c
    root,target,a,b,_=s
    t,D=k
    return (auth is not None and auth[0]==0 and auth[1]==TOKEN and auth[2]<=t
            and t>=TOKEN[2] and t<D and root==0 and target is None and not a and not b)

def dispatch(c,s,k):
    if not match(c,s) or not match(s,k):
        return UNDEF
    return guard_values(c[1],s[1],k[1])

FACTORS=(
    ('authority', (0,), token_read),
    ('physical', (1,), support_read),
    ('clock', (2,), clock_read),
    ('cut-channel-support',(0,1),match),
    ('cut-support-clock',(1,2),match),
    ('start',(0,1,2),dispatch),
)

def extract():
    a=[]; b=[]; b2=[]; bad=[]
    for x in BASES:
        a.extend(frames(x,'early-onset'))
        b.extend(frames(x,'ordinary-a'))
        b2.extend(frames(x,'ordinary-b'))
        bad.extend(frames(x,'rejected-early'))
    return a,b,b2,bad

def check():
    a,b,b2,bad=extract()
    assert len(a)==len(b)==len(b2)
    maps=[dict(zip((x[i] for x in a),(y[i] for y in b),strict=True)) for i in range(3)]
    S=[tuple(m.keys()) for m in maps]
    T=[tuple(dict.fromkeys(y[i] for y in b+b2)) for i in range(3)]
    # Each unary observation records entire receiver-facing data; exact cut
    # match tests against same-attained domains separate every distinct q.
    # Thus (q,observed payload) is exactly the section quotient, not just adequate.
    residual=lambda w:w[:2]
    seen=[]; reflections={}; rejects=0
    for i in range(3):
        assert all(x[0]==maps[i][x][0] and x[1]==maps[i][x][1] for x in S[i])
        qS={residual(maps[i][x]) for x in S[i]}
        qT={residual(y) for y in T[i]}
        assert qS==qT and len(maps[i])<len(T[i])
        # Every target index also occurs on the other side of at least one
        # incident binary match, giving its section-separating probe.
        other=1 if i!=1 else 0
        assert {x[0] for x in T[i]}=={x[0] for x in T[other]}
        seen.append(len(qT))
    for name,scope,test in FACTORS:
        n=0
        for row in product(*(S[i] for i in scope)):
            value=test(*row)
            assert value==test(*(maps[i][w] for i,w in zip(scope,row)))
            rejects+=value==UNDEF
            n+=1
        reflections[name]=n
    for x,y,z,w in zip(a,b,b2,bad,strict=True):
        for row in (x,y,z,w):
            assert dispatch(*row[:3])==row[3]
        # Induction basis is empty root grant; a common start schedules its
        # acceptance one tick later. Per-cut checks preserve admission, but
        # do not use equality of end-to-end successes as a substitute.
        assert x[3:]==y[3:]==z[3:]
        assert all(maps[i][x[i]]==y[i] for i in range(3))
    uncovered=set(residual(row[0]) for row in bad)-set(residual(row[0]) for row in a)
    assert uncovered
    witness=next((x,y) for x,y in zip(a,bad) if token_read(x[0])!=token_read(y[0]))
    assert witness[0][0][0]==witness[1][0][0]
    assert T[0][0][2]!=S[0][0][2]
    return dict(source_rows=len(a), target_rows=len(b+b2), raw_counts=[len(x) for x in T],
                residual_counts=seen, primitive_reflections=reflections,
                incompatible_ternary_rows=rejects, unmatched_early=sorted(map(repr,uncovered)),
                native_difference=[witness[0][0][2],b[0][0][2]],
                selected_independent_transfer=False)

if __name__=='__main__':
    print(json.dumps(check(),sort_keys=True,indent=2))
