#!/usr/bin/env python3
"""Independent candidate I2 codec checks; no full old-graph engine is claimed."""
from itertools import product
import json


def compose(f,g): return tuple(f[g[x]] for x in range(len(f)))

def concrete_monoid(k):
    e=tuple(range(k)); a=(k-1,1)+tuple(range(1,k-1)); b=(1,2)+(1,)*(k-2)
    found={e}; todo=[e]
    while todo:
        f=todo.pop()
        for generator in (a,b):
            h=compose(generator,f)
            if h not in found: found.add(h); todo.append(h)
    return tuple(sorted(found)),e,a,b


def encode_m(k,f):
    """Recognize concrete values, never enumerate normal forms or generator words."""
    f=tuple(f); t=k-1
    if len(f)!=k or any(type(x)!=int or not 0<=x<k for x in f): raise ValueError('not a transformation')
    if f==tuple(range(k)): return ('A',0)
    if f[1]==2 and all(x in (1,2) for x in f):
        i=sum(x==2 for x in f[1:])-1
        if f==(2,)*k: return ('B',t)
        if 0<=i<t and f[0]==1 and all(f[x]==(2 if x<=i+1 else 1) for x in range(1,k)):
            return ('B',i)
    if f[1]==1:
        i=k-f[0]
        if 1<=i<=t and all(f[x]==max(1,x-i) for x in range(1,k)):
            return ('A',i)
        i=sum(x==1 for x in f[1:])-1
        if f[0]==2 and 0<=i<=t-2 and all(f[x]==(1 if x<=i+1 else 2) for x in range(1,k)):
            return ('D',i)
    raise ValueError('outside M_k')


def decode_m(k,state):
    """Closed pointwise interpretation; independent of encoder and closure search."""
    row,i=state; t=k-1
    if row=='A' and 0<=i<=t:
        return tuple(range(k)) if i==0 else (k-i,)+tuple(max(1,x-i) for x in range(1,k))
    if row=='B' and 0<=i<=t:
        return (2,)*k if i==t else (1,)+tuple(2 if x<=i+1 else 1 for x in range(1,k))
    if row=='D' and 0<=i<=t-2:
        return (2,)+tuple(1 if x<=i+1 else 2 for x in range(1,k))
    raise ValueError('invalid normal form')


def mul_m(k,x,y):
    """Normal-form interpreter independent of concrete function composition."""
    r,i=x; s,j=y; t=k-1
    def delta(n): return ('D',n) if n<=t-2 else ('A',min(n,t))
    if r=='A':
        if i==0:return y
        return ('A',min(i+j,t)) if s=='A' else ('A',t)
    if r=='B':
        if s=='A':return ('B',min(i+j,t))
        if i:return ('B',t)
        return delta(j) if s=='B' else ('B',j)
    if s=='A':return delta(i+j)
    if i:return ('A',t)
    return ('B',j) if s=='B' else ('D',j)


def pair_mul(mul,x,y):return tuple(mul(a,b) for a,b in zip(x,y))
def swap(x):return (x[1],x[0])
def graft(mul,outer,children):
    # Lists retain occurrences, including identical values at different positions.
    return tuple(mul(a,b) for a,bs in zip(outer,children) for b in bs)


def joint_cut(carrier,mul,source,groups):
    """All paired factor tuples. ONE a per group, not one a per leaf."""
    assert sum(groups)==len(source) and all(n>0 for n in groups)
    for outer in product(carrier,repeat=len(groups)):
        options=[]; offset=0
        for a,n in zip(outer,groups):
            options.extend(tuple(b for b in carrier if mul(a,b)==x) for x in source[offset:offset+n]); offset+=n
        for flat in product(*options):
            inner=[]; offset=0
            for n in groups:inner.append(flat[offset:offset+n]);offset+=n
            yield (outer,tuple(inner))


def group_encode(x):return tuple(v%2 for v in x)
def group_observe(state):return state[0]
def group_section(state):return tuple(state) # Optional representative, NOT inverse encoder.
def add(n):return lambda a,b:tuple((x+y)%n for x,y in zip(a,b))
def map_cut(enc,cut):
    a,bs=cut
    return tuple(map(enc,a)),tuple(tuple(map(enc,b)) for b in bs)


def typed_encode(old_record,labels,encode):
    # Exact old record includes full ordered profile, frame, skeleton and empty positions.
    return old_record,tuple(encode(x) for x in labels)


def check():
    stats={'scope':'coefficient kernels and opaque exact old tags; conditional graph application','Mk':[]}
    for k in range(4,13):
        carrier,e,a,b=concrete_monoid(k); enc=lambda x:encode_m(k,x)
        codes=tuple(enc(f) for f in carrier)
        assert len(set(codes))==len(carrier)==3*k-2
        for f in carrier:assert decode_m(k,enc(f))==f
        for f,g in product(carrier,repeat=2):assert mul_m(k,enc(f),enc(g))==enc(compose(f,g))
        H={e,b,compose(b,b)}; h=lambda f:enc(f)[1]
        assert h(e)==h(b)==0 and h(compose(a,e))!=h(compose(a,b))
        # Pure C index signatures equal for e,b; left-a then index cut separates.
        signatures={f:frozenset((h(u),h(v)) for u,v in product(carrier,repeat=2) if compose(u,v)==f) for f in carrier}
        assert signatures[e]==signatures[b]
        assert (e in H)==(b in H) and ((compose(a,e) in H)==(compose(a,b) in H))
        assert signatures[compose(a,e)]!=signatures[compose(a,b)]
        for f,g in product(carrier,repeat=2):
            if h(f)==h(g):assert signatures[f]==signatures[g]
        if k==4:
            # Independent direct concrete enumeration vs table quotient interpreter.
            for source in product(carrier,repeat=2):
                expected={map_cut(enc,c) for c in joint_cut(carrier,compose,source,(2,))}
                actual=set(joint_cut(codes,lambda u,v:mul_m(k,u,v),tuple(map(enc,source)),(2,)))
                assert expected==actual
        stats['Mk'].append({'k':k,'states':len(carrier),'all_products_checked':len(carrier)**2})
    G=tuple(product(range(4),repeat=2)); Q=tuple(product(range(2),repeat=2)); gmul=add(4); qmul=add(2)
    for x in G:
        assert group_observe(group_encode(x))==x[0]%2
        assert group_encode(group_section(group_encode(x)))==group_encode(x)
    assert set(joint_cut(Q,qmul,(),()))=={((),())}
    assert set(joint_cut(Q,qmul,((0,0),),(1,)))
    for x,y in product(G,repeat=2):
        assert group_encode(gmul(x,y))==qmul(group_encode(x),group_encode(y))
        assert group_encode(swap(x))==swap(group_encode(x))
    cases=0
    for rank in range(1,5):
        # All 2^(r-1) group templates; selected rank-r source with repeated values.
        sources=list(product(G,repeat=rank)) if rank<=2 else [tuple((j%4,(j+1)%4) for j in range(rank)),((1,3),)*rank]
        for mask in range(1<<(rank-1)):
            groups=[]; n=1
            for j in range(rank-1):
                if mask>>j&1:groups.append(n);n=1
                else:n+=1
            groups.append(n);groups=tuple(groups)
            for source in sources:
                # Reference group cuts solved concretely by inverse addition, not quotient enumerator.
                expected=set()
                for outer in product(G,repeat=len(groups)):
                    bs=[]; offset=0
                    for a,n in zip(outer,groups):
                        bs.append(tuple(tuple((v-w)%4 for v,w in zip(x,a)) for x in source[offset:offset+n]));offset+=n
                    expected.add(map_cut(group_encode,(outer,tuple(bs))))
                observed=tuple(map(group_encode,source))
                actual=set(joint_cut(Q,qmul,observed,groups));assert expected==actual
                for outer,inner in actual:assert graft(qmul,outer,inner)==observed
                cases+=1
    # Graft then cut, including repeated children under one parent.
    outer=((1,2),); inner=(((2,1),(2,1),(3,0)),)
    source=graft(gmul,outer,inner); encoded=tuple(map(group_encode,source))
    assert encoded==graft(qmul,tuple(map(group_encode,outer)),tuple(tuple(map(group_encode,b)) for b in inner))
    assert map_cut(group_encode,(outer,inner)) in set(joint_cut(Q,qmul,encoded,(3,)))
    x=(3,2);assert group_section(group_encode(x))!=x
    assert group_observe(group_encode(x))==x[0]%2
    assert typed_encode(('profile-A',('active','empty','active')),(x,x),group_encode)!=typed_encode(('profile-B',('active','empty','active')),(x,x),group_encode)
    assert len(typed_encode(('profile-A',('active','empty','active')),(x,x),group_encode)[1])==2
    stats['group_shared_parent_cases']=cases
    stats['group_states_by_rank']={str(r):4**r for r in range(5)}
    stats['result']='PASS'
    return stats

if __name__=='__main__':print(json.dumps(check(),indent=2))
