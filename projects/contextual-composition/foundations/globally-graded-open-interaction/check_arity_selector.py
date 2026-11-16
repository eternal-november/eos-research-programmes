from fractions import Fraction as F
from itertools import product
import json

def arity_law(p,k):
    return {a:sum((p[i] for i in range(len(p)) if k[i]==a),F(0)) for a in sorted(set(k))}
def intervals(lam):
    out={}; c=F(0)
    for a in sorted(lam):
        out[a]=(c,c+lam[a]); c+=lam[a]
    assert c==1
    return out

def selector(ps,ks):
    if not ps:return {():F(1)}
    ls=[arity_law(p,k) for p,k in zip(ps,ks)]
    ints=[intervals(l) for l in ls]
    out={}
    for ws in product(*(range(len(p)) for p in ps)):
        ar=[k[w] for k,w in zip(ks,ws)]
        if any(l[a]==0 for l,a in zip(ls,ar)):
            out[ws]=F(0);continue
        mass=max(F(0),min(it[a][1] for it,a in zip(ints,ar))-max(it[a][0] for it,a in zip(ints,ar)))
        for p,l,a,w in zip(ps,ls,ar,ws):mass*=p[w]/l[a]
        out[ws]=mass
    assert sum(out.values())==1
    for i,p in enumerate(ps):
        for w in range(len(p)):
            assert sum(v for ws,v in out.items() if ws[i]==w)==p[w]
    return out
p=[F(1,4),F(1,4),F(1,2),F(0)];k=[1,1,2,3]
q=[F(1,3),F(1,6),F(1,2)];h=[1,2,2]
s=selector([p,q],[k,h])
r=[0,0,1,2];t=[0,1,1]
p2=[F(1,2),F(1,2),F(0)];k2=[1,2,3]
q2=[F(1,3),F(2,3)];h2=[1,2]
target=selector([p2,q2],[k2,h2]);push={w:F(0) for w in target}
for (i,j),v in s.items():push[r[i],t[j]]+=v
assert push==target
fair=selector([[F(1,2)]*2]*2,[[1,2]]*2)
assert fair=={(0,0):F(1,2),(0,1):F(0),(1,0):F(0),(1,1):F(1,2)}
assert selector([],[])=={():F(1)}
# Actual three-stage source associativity diagnostic, all raw zeros retained.
fairp=[F(1,2),F(1,2)]
local=[]; plocal=[]; klocal=[]
for a in (1,2):
    inner=selector([fairp]*a,[[1,2]]*a)
    for hs in product((1,2),repeat=a):
        local.append((a,hs));plocal.append(F(1,2)*inner[tuple(b-1 for b in hs)]);klocal.append(sum(hs))
rightq=selector([plocal,plocal],[klocal,klocal])
right={(local[i],local[j]):v for (i,j),v in rightq.items()}
left={}
gq=selector([fairp,fairp],[[1,2],[1,2]])
for aa in product((1,2),repeat=2):
    hq=selector([fairp]*sum(aa),[[1,2]]*sum(aa))
    for hh in product((1,2),repeat=sum(aa)):
        tree=((aa[0],hh[:aa[0]]),(aa[1],hh[aa[0]:]))
        left[tree]=gq[tuple(a-1 for a in aa)]*hq[tuple(b-1 for b in hh)]
assert left.keys()==right.keys() and len(left)==36
assert sorted(v for v in left.values() if v)==[F(1,4)]*4
assert sorted(v for v in right.values() if v)==[F(1,8)]*4+[F(1,4)]*2
assert sum(left.values())==sum(right.values())==1
result={'status':'passed','checks':['normalization','all-marginals','arity-preserving-independent-raw-merges','zero-arity-stratum-retained','fair-unary-binary-nonproduct','nullary-unit','associativity-weight-multiset-obstruction'],'associativity':{'full_raw_trees':36,'left_positive_weights':['1/4']*4,'right_positive_weights':['1/4']*2+['1/8']*4},'scope':'finite exact diagnostics; associativity counterexample at specified three-stage source'}
print(json.dumps(result,indent=2))
