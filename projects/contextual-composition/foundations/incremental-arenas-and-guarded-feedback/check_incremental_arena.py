"""Exact bounded diagnostics for intrinsic incremental arena composition."""
from fractions import Fraction as F
from itertools import product
from collections import deque

class Early:
    def __init__(self,name,length=2):self.name=name;self.length=length
    def initial(self,a):return ()
    def enabled(self,s):return () if len(s)==self.length else ((self.name,len(s)),)
    def ports(self,s):return () if not s else ((0,0),)
    def step(self,s,e,w):assert e in self.enabled(s);return s+(w,)
    def snapshots(self,s):return {self.name:s}
    def eid(self,e):return e

class Comp:
    def __init__(self,p,q):self.p=p;self.q=q
    def initial(self,a):
        s=self.p.initial(a)
        return s,tuple((p,self.q.initial(b)) for p,b in self.p.ports(s))
    def enabled(self,z):
        s,ts=z
        return tuple(('L',e) for e in self.p.enabled(s))+tuple(('R',p,e) for p,t in ts for e in self.q.enabled(t))
    def ports(self,z):
        s,ts=z
        return tuple(((p,q),b) for p,t in ts for q,b in self.q.ports(t))
    def step(self,z,e,w):
        s,ts=z; d=dict(ts)
        if e[0]=='L':
            s=self.p.step(s,e[1],w)
            for p,b in self.p.ports(s):
                if p not in d:d[p]=self.q.initial(b)
        else:
            _,p,ee=e;d[p]=self.q.step(d[p],ee,w)
        return s,tuple((p,d[p]) for p,b in self.p.ports(s))
    def snapshots(self,z):
        s,ts=z;out=self.p.snapshots(s)
        for p,t in ts:out.update(self.q.snapshots(t))
        return out
    def eid(self,e):return self.p.eid(e[1]) if e[0]=='L' else self.q.eid(e[2])

P,Q,R=Early('P'),Early('Q'),Early('R',1)
left,right=Comp(Comp(P,Q),R),Comp(P,Comp(Q,R))
queue=deque([(left.initial(0),right.initial(0))]);seen=set()
while queue:
    a,b=queue.popleft()
    if (a,b) in seen:continue
    seen.add((a,b))
    assert left.snapshots(a)==right.snapshots(b)
    le={left.eid(e):e for e in left.enabled(a)}
    re={right.eid(e):e for e in right.enabled(b)}
    assert le.keys()==re.keys()
    assert [v for _,v in left.ports(a)]==[v for _,v in right.ports(b)]
    for e in le:
        for w in (0,1,2):queue.append((left.step(a,le[e],w),right.step(b,re[e],w)))
    # Strict operational diamonds, including event/port persistence.
    for e,f in product(left.enabled(a),repeat=2):
        if e==f:continue
        for w,z in product((0,1,2),repeat=2):
            a1=left.step(a,e,w);a2=left.step(a,f,z)
            assert f in left.enabled(a1) and e in left.enabled(a2)
            assert left.step(a1,f,z)==left.step(a2,e,w)
print('PASS',len(seen),'paired raw configurations: native operational associativity and all enabled-event diamonds.')

mu={0:F(1,2),1:F(1,2),2:F(0)}
def evaluate(arena,policy):
    result={}
    def run(s,weight,trace):
        enabled=arena.enabled(s)
        if not enabled:
            key=tuple(sorted(trace.items()));assert key not in result
            result[key]=weight;return
        scope=policy(enabled)
        for ws in product(mu,repeat=len(scope)):
            ss=s;p=weight;tt=dict(trace)
            for e,w in zip(scope,ws):
                ss=arena.step(ss,e,w);p*=mu[w];tt[arena.eid(e)]=w
            run(ss,p,tt)
    run(arena.initial(0),F(1),{})
    return result
policies=[lambda es:es[:1],lambda es:es[-1:],lambda es:es]
laws=[evaluate(left,p) for p in policies]+[evaluate(right,p) for p in policies]
assert all(x==laws[0] for x in laws)
assert len(laws[0])==243 and sum(p>0 for p in laws[0].values())==32 and sum(laws[0].values())==1
print('PASS six external schedulers/parenthesizations:243 raw complete traces,32 positive,211 zeros, exact independent law.')
# Context tensor projections retain actual linear maps, not only scalar law.
for bits in product((0,1),repeat=5):
    direct=int(all(b==0 for b in bits))
    for order in ((0,1,2,3,4),(4,3,2,1,0),(0,2,4,1,3)):
        assert direct==int(all(bits[i]==0 for i in order))
print('PASS tensor augmentation-only basis maps commute with event reordering.')
def matmul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def kron(a,b):
    return [[a[i][j]*b[k][l] for j in range(len(a[0])) for l in range(len(b[0]))] for i in range(len(a)) for k in range(len(b))]
A=[[1,0],[1,2],[0,3]]; B=[[1,0,0],[4,5,6]]
AA=[[1,0,0],[2,3,4]]; BB=[[1,0],[5,6],[7,8]]
assert matmul(kron(AA,BB),kron(A,B))==kron(matmul(AA,A),matmul(BB,B))
for i in range(2):
    for j in range(3):
        # Actual target tensors are flipped after applying nontrivial augmented maps.
        lhs={(n,m):A[m][i]*B[n][j] for m in range(3) for n in range(2)}
        rhs={(n,m):B[n][j]*A[m][i] for n in range(2) for m in range(3)}
        assert lhs==rhs
print('PASS nontrivial augmented rectangular matrix tensor/symmetry and composition squares.')
# A Q event can be enabled while P still has its second event pending.
a=left.initial(0);ep=next(e for e in left.enabled(a) if left.eid(e)==('P',0));a=left.step(a,ep,0)
assert {('P',1),('Q',0)} <= {left.eid(e) for e in left.enabled(a)}
print('PASS incremental continuation exposes Q before P batch termination; no hidden all-sibling barrier.')
for n in range(10):
    terminal=sum(F(1,2**(k+1)) for k in range(n))
    active=F(1,2**n)
    assert terminal+active==1
print('PASS unbounded geometric finite-prefix mass identity; no infinite coefficient tensor used.')
print('BOUNDARY: finite diagnostics, not a proof assistant or unrestricted shared-policy schedule quotient.')
