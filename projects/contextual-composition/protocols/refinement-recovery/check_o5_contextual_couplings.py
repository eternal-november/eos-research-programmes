#!/usr/bin/env python3
"""Independent exact finite diagnostics for O5; not an all-context proof.
Run with Python 3. Standard library only. All probabilities are Fractions.
"""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
import json
from pathlib import Path

def law(items):
    d=defaultdict(F)
    for x,p in items: d[x]+=p
    return {x:p for x,p in d.items() if p}
def push(d,f): return law((f(x),p) for x,p in d.items())
def prod(ds):
    return law((tuple(x for x,p in xs), __import__('functools').reduce(lambda a,b:a*b,(p for x,p in xs),F(1))) for xs in product(*(list(d.items()) for d in ds)))
def marg(d,i): return push(d,lambda x:x[i])
def leaf(x): return ('L',x)
def node(k,*cs): return ('N',k,cs)
def leaves(t): return [t[1]] if t[0]=='L' else [x for c in t[2] for x in leaves(c)]
def graft(t,ts):
    it=iter(ts)
    def go(t): return next(it) if t[0]=='L' else node(t[1],*(go(c) for c in t[2]))
    r=go(t)
    assert next(it,None) is None
    return r
def tmap(t,f): return leaf(f(t[1])) if t[0]=='L' else node(t[1],*(tmap(c,f) for c in t[2]))
def pairtree(t,u):
    assert t[0]==u[0]
    if t[0]=='L': return leaf((t[1],u[1]))
    assert t[1]==u[1] and len(t[2])==len(u[2])
    return node(t[1],*(pairtree(a,b) for a,b in zip(t[2],u[2])))
def lift(p,q,a,b,g):
    mu,nu=push(p,a),push(q,b)
    return law(((w,v),g.get((a(w),b(v)),F(0))*pw/mu[a(w)]*qv/nu[b(v)])
               for w,pw in p.items() for v,qv in q.items() if pw and qv)
def glue(g,d):
    nu=marg(g,1); assert nu==marg(d,0)
    return law(((x,y,z),p*q/nu[y]) for (x,y),p in g.items() for (yy,z),q in d.items() if y==yy and nu.get(y,0))
def outcome(c,b,j=None): return (c,leaf((b,b if j is None else (b,j))))
def related(o,p):
    if o[0]>p[0]: return False
    t=pairtree(o[1],p[1])
    return all(a[0]==b[0] and a[1]==b[1][0] for a,b in leaves(t))

results={}
# Raw histories duplicate both outcome classes and contain a zero path.
p={'p00':F(1,6),'p01':F(1,3),'p10':F(1,2),'pzero':F(0)}
q={'q000':F(1,8),'q001':F(1,8),'q01':F(1,4),'q10':F(1,4),'q11':F(1,4),'qzero':F(0)}
a=lambda w:outcome(1,int(w[1])) if w!='pzero' else outcome(99,0)
b=lambda w:outcome(2,int(w[1]),int(w[2])) if w!='qzero' else outcome(100,0,0)
g={(outcome(1,i),outcome(2,i,j)):F(1,4) for i,j in product(range(2),repeat=2)}
G=lift(p,q,a,b,g)
assert marg(G,0)=={w:v for w,v in p.items() if v}
assert marg(G,1)=={w:v for w,v in q.items() if v}
assert push(G,lambda w:(a(w[0]),b(w[1])))==g
for (w,v),weight in G.items():
    ap,bq=a(w),b(v); assert related(ap,bq)
    common_body=pairtree(ap[1],bq[1]); common_cost=bq[0]
    assert tmap(common_body,lambda z:z[0])==ap[1]
    assert tmap(common_body,lambda z:z[1])==bq[1]
    assert ap[0]<=common_cost==bq[0]
results['raw_lift']={'positive_common_histories':len(G),'candidate_raw_rows':len(p),'reference_raw_rows':len(q),'zero_rows_omitted':2,'mass_body_and_cost_checks':True}
# Two further couplings, including genuine nonfunctional middle gluing.
d=law(((y,(3,y[1][1][0],k)),mass*F(1,2)) for y,mass in marg(g,1).items() for k in range(2))
e=law(((z,(4,z[1],h)),mass*F(1,2)) for z,mass in marg(d,1).items() for h in range(2))
h=glue(g,d)
# Explicit zero-mass middle witness exercises the denominator guard.
gzero=dict(g); dzero=dict(d)
gzero[('zero_x','zero_y')]=F(0); dzero['zero_y','zero_z']=F(0)
assert glue(gzero,dzero)==h
assert push(h,lambda z:z[:2])==g and push(h,lambda z:z[1:])==d
left=law(((x,y,z,w),p*e[z,w]/marg(d,1)[z]) for (x,y,z),p in h.items() for zz,w in e if zz==z)
right=law(((x,y,z,w),p*g[x,y]/marg(g,1)[y]) for (y,z,w),p in glue(d,e).items() for x,yy in g if yy==y)
assert left==right
results['vertical_gluing']={'triple_witnesses':len(h),'quadruple_witnesses':len(left),'marginals_and_reassociation':True,'zero_middle_rows_ignored':True}
# Generic algebraic occurrence-indexed tree bind, separately interpreted marginals.
# Leaf states are distinct occurrence-indexed private carriers, NOT cloned tokens.
# Repeated value labels test occurrence indexing; this fixture is not a typechecker.
def bind_dist(prefix,kernel):
    return law(((c+sum(o[0] for o in os),graft(t,[o[1] for o in os])),p*w)
        for (c,t),p in prefix.items() for os,w in prod([kernel(x) for x in leaves(t)]).items())
def coupled_bind(prefix,kernel):
    rows=[]
    for ((cp,tp),(cq,tq)),p in prefix.items():
        paired=pairtree(tp,tq)
        for os,w in prod([kernel(x,y) for x,y in leaves(paired)]).items():
            aa=[o[0] for o in os]; bb=[o[1] for o in os]
            rows.append((((cp+sum(o[0] for o in aa),graft(tp,[o[1] for o in aa])),
                          (cq+sum(o[0] for o in bb),graft(tq,[o[1] for o in bb]))),p*w))
    return law(rows)
def local(x,y):
    assert x[0]==y[0] and x[1]==y[1][0]
    return {((1,leaf((r,x[1]))),(2,leaf((r,(y[1][0],j))))):F(1,4) for r,j in product(range(2),repeat=2)}
def kp(x): return {(1,leaf((r,x[1]))):F(1,2) for r in range(2)}
def kq(y): return {(2,leaf((r,(y[1][0],j)))):F(1,4) for r,j in product(range(2),repeat=2)}
counts=[]
for arity in range(4):
    # Dict collisions for nullary trees must aggregate rather than overwrite.
    prefix=law((((1,node('Fork',*(leaf((b,b)) for _ in range(arity)))),(2,node('Fork',*(leaf((b,(b,j))) for _ in range(arity))))),F(1,4)) for b,j in product(range(2),repeat=2))
    joint=coupled_bind(prefix,local)
    assert marg(joint,0)==bind_dist(marg(prefix,0),kp)
    assert marg(joint,1)==bind_dist(marg(prefix,1),kq)
    assert sum(joint.values())==1 and all(related(x,y) for x,y in joint)
    counts.append(len(joint))
results['horizontal_bind']={'arities':[0,1,2,3],'joint_outcome_counts':counts,'repeated_leaf_occurrences':True,'nullary_empty_product':True,'marginals_body_cost':True}
# Exhaustive finite adaptive public controllers, persistent private states.
# Leaves return a public bool; query branches choose a different continuation.
def controllers(depth):
    if depth==0:return [('ret',0),('ret',1)]
    prior=controllers(depth-1)
    return [('ret',0),('ret',1)]+[('call',l,r) for l,r in product(prior,repeat=2)]
def run(t,state,ref=False):
    if t[0]=='ret':return {(0,leaf((t[1],state))):F(1)}
    bit=state[0] if ref else state
    # Reference refreshes junk on each call; candidate preserves its bit.
    return law(((cost+(2 if ref else 1),node('Read',body)),p*w)
       for s,w in ([( (bit,j),F(1,2)) for j in range(2)] if ref else [(state,F(1))])
       for (cost,body),p in run(t[1+bit],s,ref).items())
def crun(t,b,bj):
    if t[0]=='ret':return {((0,leaf((t[1],b))),(0,leaf((t[1],bj)))):F(1)}
    assert b==bj[0]
    return law((((cp+1,node('Read',tp)),(cq+2,node('Read',tq))),p*F(1,2))
        for j in range(2) for ((cp,tp),(cq,tq)),p in crun(t[1+b],b,(b,j)).items())
cs=controllers(3); cases=0; supports=0
for t in cs:
    joint=law((pair,p*F(1,4)) for b,j in product(range(2),repeat=2) for pair,p in crun(t,b,(b,j)).items())
    pl=law((o,p*F(1,2)) for b in range(2) for o,p in run(t,b).items())
    ql=law((o,p*F(1,4)) for b,j in product(range(2),repeat=2) for o,p in run(t,(b,j),True).items())
    assert marg(joint,0)==pl and marg(joint,1)==ql
    assert all(related(x,y) for x,y in joint)
    cases+=1;supports+=len(joint)
results['adaptive_clients']={'depth_bound':3,'enumerated_controllers':cases,'positive_coupling_entries':supports,'separate_interpreters_match':True,'private_state_persisted':True,'cost_candidate_1_reference_2':True}
# Disjoint batch: fresh child products conditioned on one correlated joint store.
init=law((((b,b),((b,j),(b,k))),F(1,8)) for b,j,k in product(range(2),repeat=3))
def read_pair(b,bj):
    assert b==bj[0]
    return {((1,leaf((b,b))),(2,leaf((b,(b,j))))):F(1,2) for j in range(2)}
batch=law((((sum(x[0][0] for x in os),node('Fork2',*(x[0][1] for x in os))),
            (sum(x[1][0] for x in os),node('Fork2',*(x[1][1] for x in os)))),p*w)
          for (ss,tt),p in init.items()
          for os,w in prod([read_pair(ss[i],tt[i]) for i in range(2)]).items())
expected_p=push(marg(init,0),lambda ss:(2,node('Fork2',*(leaf((b,b)) for b in ss))))
expected_q=law(((4,node('Fork2',*(leaf((tt[i][0],(tt[i][0],js[i]))) for i in range(2)))),p*F(1,4))
               for tt,p in marg(init,1).items() for js in product(range(2),repeat=2))
assert marg(batch,0)==expected_p and marg(batch,1)==expected_q
assert all(related(x,y) for x,y in batch)
assert all(leaves(o[1])[0][0]==leaves(o[1])[1][0] for o in marg(batch,0))
results['correlated_positive_batch']={'joint_initial_pairs':len(init),'joint_outcomes':len(batch),'conditional_child_products_preserve_initial_correlation':True,'marginals_and_cost_checked':True}

# Negative tests computed from actual finite executions, not expected-only rows.
shared=law(((b,b),F(1,2)) for b in range(2))
fresh=prod([{0:F(1,2),1:F(1,2)}]*2)
assert marg(shared,0)==marg(fresh,0) and marg(shared,1)==marg(fresh,1)
agree=lambda d:sum(p for (x,y),p in d.items() if x==y)
assert agree(shared)!=agree(fresh)
# Fork reads two actual disjoint token entries from one JOINT store law.
def fork_read(init): return push(init,lambda s:node('Fork2',leaf(('token_a',s[0])),leaf(('token_b',s[1]))))
correlated,independent=fork_read(shared),fork_read(fresh)
assert correlated!=independent
results['negative_shared_fresh']={'shared_two_call_agreement':str(agree(shared)),'fresh_two_call_agreement':str(agree(fresh)),'one_call_marginals_equal':True}
results['negative_joint_initialization']={'same_bit_fork_agreement':str(agree(shared)),'independent_fork_agreement':str(agree(fresh)),'individual_token_marginals_equal':True,'fork_laws_differ':correlated!=independent,'product_relation_not_independence':True}
# Cost-exact native projection may omit zero candidate history; law bound != raw bound.
zero_candidate={'ok':(F(1),1),'bad_zero':(F(0),99)}
reference={'ok':(F(1),1)}
covered={'ok'}
assert law((c,p) for p,c in zero_candidate.values())==law((c,p) for p,c in reference.values())
assert max(c for p,c in reference.values())==1 and max(c for p,c in zero_candidate.values())==99
assert set(zero_candidate)-covered=={'bad_zero'}
results['negative_zero_coverage']={'same_law':True,'reference_all_path_max':1,'candidate_all_path_max':99,'uncovered_candidate_rows':['bad_zero'],'reference_projection_coverage_insufficient':True}
results['scope']='Exact finite regression diagnostics only; no enumeration proves the quantified O4 all-context theorem or a full typechecker.'
results['status']='PASS'
out=Path(__file__).with_name('o5_contextual_results.json');out.write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
