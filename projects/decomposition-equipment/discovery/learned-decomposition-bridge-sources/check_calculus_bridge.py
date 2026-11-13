"""Bounded regressions only; not a proof of the Borel theorem."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from pathlib import Path
import json, random

rng=random.Random(20261028)
counts={'scope_families':0,'state_split_bijections':0,'event_split_bijections':0,'joined_tuples':0}

def tab(scope, alphabet, constraints=()):
    s=tuple(sorted(scope))
    return [dict(zip(s,v)) for v in product(range(alphabet),repeat=len(s))
            if all(pred(dict(zip(s,v))) for pred in constraints)]
def key(a, scope): return tuple(a[j] for j in sorted(scope))

for case in range(220):
    d=rng.randint(1,4); n=rng.randint(2,5)
    scopes=[{j for j in range(d) if rng.randrange(2)} for _ in range(n)]
    for j in range(d):
        if not any(j in s for s in scopes): scopes[rng.randrange(n)].add(j)
    first={j:min(i for i in range(n) if j in scopes[i]) for j in range(d)}
    last={j:max(i for i in range(n) if j in scopes[i]) for j in range(d)}
    B=[{j for j in range(d) if first[j]<k<=last[j]} for k in range(n+1)]
    bags=[scopes[k]|B[k]|B[k+1] for k in range(n)]
    # Some owner-local event constraints. These restrict edges, not states.
    constraints=[]
    for k in range(n):
        ss=sorted(scopes[k])
        constraints.append((lambda a,ss=ss: (a[ss[0]]%2)==(a[ss[1]]%2))
                           if len(ss)>=2 and rng.randrange(3)==0 else (lambda a: True))
    for alphabet, kind in [(2,'state'),(4,'event')]:
        cache={}
        for i in range(n):
            for j in range(i+1,n+1):
                scope=set().union(*bags[i:j])
                tests=constraints[i:j] if kind=='event' else ()
                cache[i,j]=(scope,tab(scope,alphabet,tests))
        for i in range(n):
            for k in range(i+1,n):
                for j in range(k+1,n+1):
                    ls,L=cache[i,k]; rs,R=cache[k,j]; ws,W=cache[i,j]
                    assert ls & rs == B[k]
                    index=defaultdict(list)
                    for r in R: index[key(r,B[k])].append(r)
                    joined=[]
                    for l in L:
                        for r in index[key(l,B[k])]:
                            out=l|r
                            assert len(out)==len(ws)
                            joined.append(key(out,ws))
                    expected=[key(w,ws) for w in W]
                    assert sorted(joined)==sorted(expected)
                    assert len(set(joined))==len(joined)
                    # Event source and target commute with projections.
                    if kind=='event':
                        for w in W:
                            for ss in (ls,rs):
                                assert tuple((w[q]//2) for q in sorted(ss)) == key({q:w[q]//2 for q in ws},ss)
                                assert tuple((w[q]%2) for q in sorted(ss)) == key({q:w[q]%2 for q in ws},ss)
                    counts[kind+'_split_bijections']+=1
                    counts['joined_tuples']+=len(joined)
    counts['scope_families']+=1

# Common-source prior is owned once; duplicated source changes the law.
shared={}; independent={}
for c,n1,n2 in product(range(2),repeat=3):
    w=F(1,2)*(F(1,4) if n1 else F(3,4))*(F(1,4) if n2 else F(3,4))
    xy=(c^n1,c^n2); shared[xy]=shared.get(xy,F(0))+w
for c1,c2,n1,n2 in product(range(2),repeat=4):
    w=F(1,4)*(F(1,4) if n1 else F(3,4))*(F(1,4) if n2 else F(3,4))
    xy=(c1^n1,c2^n2); independent[xy]=independent.get(xy,F(0))+w
assert all(x>0 for x in shared.values())
assert sum(shared.values())==1 and sum(independent.values())==1
assert shared[0,0]+shared[1,1]==F(5,8)
assert independent[0,0]+independent[1,1]==F(1,2)
double_prior_total=sum(F(1,4)*(F(1,4) if n1 else F(3,4))*(F(1,4) if n2 else F(3,4)) for c,n1,n2 in product(range(2),repeat=3))
assert double_prior_total==F(1,2)

# Non-product local split and persistent path law; initializer applied once.
pi=[F(x,10) for x in (1,2,3,4)]
def q(s,x): return F(1+((x+s)%4),10)
def children(s,b0,b1):
    marg=sum(q(s,2*b0+j) for j in range(2))
    cond=q(s,2*b0+b1)/marg
    return marg*cond
path_count=0; total=F(0); perm=(2,0,3,1)
for path in product(range(4),repeat=5):
    p=pi[path[0]]; r=pi[path[0]]
    for s,x in zip(path,path[1:]):
        p*=q(s,x); r*=children(s,x//2,x%2)
    assert p==r
    transformed=tuple(perm[x] for x in path)
    inv={y:x for x,y in enumerate(perm)}
    assert tuple(inv[y] for y in transformed)==path
    total+=p; path_count+=1
assert total==1
# Growing Gaussian-ring example: exact rank conditions on polynomial means.
def rank(rows):
    a=[[F(x) for x in row] for row in rows]; r=0
    if not a: return 0
    for c in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][c]),None)
        if pivot is None: continue
        a[r],a[pivot]=a[pivot],a[r]
        z=a[r][c]; a[r]=[x/z for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][c]:
                z=a[i][c]; a[i]=[x-z*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a): break
    return r
ring_checks=[]
for m in range(3,13):
    means=[]; jac=[]
    for j in range(m):
        for sign in (1,-1):
            v=[0]*m; v[j]=1; v[(j+1)%m]=sign; means.append(v)
            d=[0]*(2*m); d[j]=2*sign; d[m+j]=3; jac.append(d)
    assert rank(means)==m and rank(jac)==2*m
    assert all({i,(i-1)%m}&{i,(i+1)%m}=={i} for i in range(m))
    ring_checks.append({'m':m,'mean_rank':m,'jacobian_rank':2*m})
out={'status':'PASS','scope':'bounded finite rational regressions, not proof of standard Borel theorem',
     **counts,'weighted_four_step_paths':path_count,
     'shared_equal_probability':str(shared[0,0]+shared[1,1]),
     'duplicated_source_equal_probability':str(independent[0,0]+independent[1,1]),
     'duplicated_prior_total_mass':str(double_prior_total),
     'persistent_path_total_mass':str(total),'growing_ring_rank_checks':ring_checks}
Path(__file__).with_name('Calculus_Bridge_Checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
