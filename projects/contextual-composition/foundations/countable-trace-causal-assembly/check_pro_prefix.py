from itertools import product
from pathlib import Path
import re
# Full grade grammar: None is P0 seed, B is settled variable,
# ('U',label,subtree) is a constant-labelled continuing child.
C=((0,'z'),(1,'u'),(1,'v'),(2,'b'))
U=(0,1)
def grades(n):
    if n==0:return [None]
    child=['B']+[('U',u,t) for u in U for t in grades(n-1)]
    return [(c,tuple(xs)) for c in C for xs in product(child,repeat=c[0])]
def prune(t,n):
    if n==0:return None
    c,ch=t
    return (c,tuple(x if x=='B' else ('U',x[1],prune(x[2],n-1)) for x in ch))
def leaves(t,p=()):
    if t is None:return []
    ans=[]
    for i,x in enumerate(t[1]):
        if x=='B':ans.append(p+(i,))
        else:ans+=leaves(x[2],p+(i,))
    return ans
def nodes(t,p=()):
    if t is None:return []
    return [p]+[v for i,x in enumerate(t[1]) if x!='B' for v in nodes(x[2],p+(i,))]
def native_shape(t):
    if t is None:return None
    c,ch=t
    # Merge both unary content tags and both U labels, preserve ordered slots.
    c=(c[0], 'u' if c[0]==1 else c[1])
    return (c,tuple(x if x=='B' else ('U',0,native_shape(x[2])) for x in ch))
G=grades(2)
for t in G:
    for n in range(3):
        p=prune(t,n)
        assert set(leaves(p))<=set(leaves(t))
        assert native_shape(p)==prune(native_shape(t),n)
        for m in range(n,3):
            assert prune(prune(t,m),n)==p
            # Backward slot maps compose as address inclusions.
            assert [leaves(t).index(x) for x in leaves(p)]==[
                leaves(t).index(leaves(prune(t,m))[j]) for j in
                [leaves(prune(t,m)).index(x) for x in leaves(p)]]
            # Content tensor augmentation on e0/e1 basis: deleted e1 ->0.
            ns=nodes(t); mid=nodes(prune(t,m)); end=nodes(p)
            for bits in product((0,1),repeat=len(ns)):
                data=dict(zip(ns,bits))
                direct=None if any(data[v] for v in ns if v not in end) else tuple(data[v] for v in end)
                first=None if any(data[v] for v in ns if v not in mid) else {v:data[v] for v in mid}
                staged=None if first is None or any(first[v] for v in mid if v not in end) else tuple(first[v] for v in end)
                assert direct==staged
print(f'PASS all {len(G)} full horizon2 shapes: pruning, backward positions, merged grade/state maps, actual basis augmentation composition')
# Scalar native truncation including all zero histories, bounded finite probe.
from fractions import Fraction as F
rows=[((),1,F(1))]
for n in range(3):
    nxt=[]
    for h,active,m in rows:
        if active==0:
            nxt.append((h,active,m)); continue
        draws=list(product((0,1),repeat=active))
        local=[]
        for draw in draws:
            q=F(1,2) if len(set(draw))==1 else F(0)
            local.append((h+(draw,),2*sum(draw),m*q))
        assert sum(x[2] for x in local)==m
        nxt+=local
    assert sum(x[2] for x in nxt)==1
    rows=nxt
assert any(x[2]==0 for x in rows)
print('PASS exact normalized raw prefix-fibre pushforward (terminal absorption)')
s=Path(__file__).with_name('Augmented_Polynomial_Pro_Prefix_Semantics.tex').read_text();st=[]
for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
    if op=='begin':st.append(name)
    else:assert st.pop()==name
assert not st
print('PASS TeX environment nesting; no compilation/formal verification claimed')
# Two augmented root arrows, equal after later zero-domain transition.
f=((1,),(0,)); g=((1,),(1,))
assert f!=g
assert f[0]==g[0]==(1,)
# Matrices from the zero vector space have no columns, independently of f/g.
assert tuple(() for row in f)==tuple(() for row in g)==((),())
print('PASS explicit augmented root-map distinction and zero-domain collapse')
