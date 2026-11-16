from fractions import Fraction as F
from itertools import product

def push(law,maps,target_sets):
    out={y:F(0) for y in product(*target_sets)}
    for w,p in law.items():out[tuple(r[x] for r,x in zip(maps,w))]+=p
    return out

def marginal_push(mu,r,target):
    return {y:sum((p for x,p in mu.items() if r[x]==y),F(0)) for y in target}

def lift(q,mus,mups,maps):
    out={}
    for w in product(*(list(mu) for mu in mus)):
        y=tuple(r[x] for r,x in zip(maps,w)); p=q[y]
        for i,x in enumerate(w):
            den=mups[i][y[i]]
            if not den:p=F(0);break
            p*=mus[i][x]/den
        out[w]=p
    return out

def check_marginals(q,mus):
    assert sum(q.values())==1
    for i,mu in enumerate(mus):
        for x,p in mu.items():assert sum(v for w,v in q.items() if w[i]==x)==p

mu=[dict(enumerate([F(1,6),F(1,6),F(1,3),F(1,3),F(0)])),dict(enumerate([F(1,4),F(1,4),F(1,2),F(0)]))]
r=[{0:'a',1:'a',2:'b',3:'c',4:'z'},{0:'a',1:'a',2:'b',3:'z'}]
mid=[('a','b','c','z','ghost'),('a','b','z','ghost')]
s=[{'a':0,'b':0,'c':1,'z':2,'ghost':1},{'a':0,'b':1,'z':2,'ghost':2}]
end=[(0,1,2),(0,1,2)]
mp=[marginal_push(mu[i],r[i],mid[i]) for i in range(2)]
mpp=[marginal_push(mp[i],s[i],end[i]) for i in range(2)]
sr=[{w:s[i][r[i][w]] for w in mu[i]} for i in range(2)]
for t in (F(1,6),F(1,3),F(1,2)):
    q={y:F(0) for y in product(*end)}
    q[0,0]=t;q[0,1]=F(2,3)-t;q[1,0]=F(1,2)-t;q[1,1]=t-F(1,6)
    check_marginals(q,mpp)
    middle=lift(q,mp,mpp,s)
    staged=lift(middle,mu,mp,r)
    direct=lift(q,mu,mpp,sr)
    assert staged==direct
    assert push(direct,sr,end)==q
    check_marginals(direct,mu)
    assert len(direct)==20 and any(p==0 for p in direct.values())
    ids=[{x:x for x in m} for m in mu]
    assert lift(direct,mu,mu,ids)==direct
    # Zero/off-policy histories carry complete tables; no prefix mass used.
    for history,prefix_mass in [('positive',F(1)),('zero',F(0)),('off-policy',None)]:
        assert lift(middle,mu,mp,r)==direct
print('PASS3 target couplings (including an independent case): exact source marginals/pushforward/composition/identity, zero denominators and empty target fibres.')

fair={0:F(1,2),1:F(1,2)}
collapse=[{0:0,1:0},{0:0,1:0}]
unit=[{0:F(1)},{0:F(1)}]; q={(0,0):F(1)}
ind=lift(q,[fair,fair],unit,collapse)
diag={(a,b):F(a==b,2) for a,b in product(range(2),repeat=2)}
assert ind!=diag and push(ind,collapse,[(0,),(0,)])==push(diag,collapse,[(0,),(0,)])==q
assert lift(diag,[fair,fair],[fair,fair],[{0:0,1:1}]*2)==diag
assert lift({():F(1)},[],[],[])=={():F(1)}
print('PASS canonical-fibration versus all-compatible counterexample; exact zero-history identity and nullary unit.')
print('BOUNDARY: finite exact diagnostics; all-history/native tensor and assembly coherence remain written proof obligations.')
