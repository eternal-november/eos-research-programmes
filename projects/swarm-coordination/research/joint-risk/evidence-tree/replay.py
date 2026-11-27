"""Whole-law OR-cohort admission with exact tree projection and LP cross-check."""
from collections import defaultdict
from itertools import product
from random import Random
import json

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

def margin(root,arm="global",cap=0.0):
    seen=bool(root&1)
    fail=bool(root&(4 if seen else 2))
    if arm=="global":return float(fail)
    if arm=="quiet_joint":return float(fail and not seen)
    if arm=="seen_joint":return float(fail and seen)
    if arm=="quiet_cond":return (float(fail)-cap) if not seen else 0.
    if arm=="seen_cond":return (float(fail)-cap) if seen else 0.
    if arm=="new_only":return float(seen and bool(root&8))
    raise ValueError(arm)

def full(par,mask,p,q,target):
    items=list(product((0,1),repeat=len(par)))
    flags=[0]*len(items)
    for j,x in enumerate(items):
        for bit,tag in zip(x,mask):
            if bit:flags[j]|=tag
    rows=[[1]*len(items)]
    rhs=[1.]
    for i in range(len(par)):
        rows.append([x[i] for x in items]);rhs.append(p[i])
        if i:
            rows.append([x[i]*x[par[i]] for x in items]);rhs.append(q[i])
    return rows,rhs,[target(x) for x in flags],flags

def factored(par,mask,p,q,target):
    n=len(par)
    ch=[[] for i in par]
    for i,pa in enumerate(par):
        if i:ch[pa].append(i)
    S=[set() for _ in par]
    tables=[[] for _ in par]
    for i in reversed(range(n)):
        for kids in product(*(sorted(S[j]) for j in ch[i])):
            descendant=0
            for _,flag in kids:descendant|=flag
            for bit in (0,1):
                st=bit,descendant|(mask[i] if bit else 0)
                S[i].add(st)
                tables[i].append((st,kids))
    offset=[0]
    for t in tables:offset.append(offset[-1]+len(t))
    ids=[[] for _ in par]
    for i in range(n):
        ids[i]=list(zip(range(offset[i],offset[i+1]),tables[i]))
    row=[];col=[];value=[];rhs=[]
    def append(terms,b):
        for a,c in terms:
            row.append(len(rhs));col.append(a);value.append(c)
        rhs.append(b)
    append(((a,1) for a,_ in ids[0]),1.)
    for i in range(n):
        append(((a,1) for a,(st,k) in ids[i] if st[0]),p[i])
        for k,j in enumerate(ch[i]):
            for s in S[j]:
                append([(a,1) for a,(x,kids) in ids[i] if kids[k]==s]
                     + [(a,-1) for a,(x,kids) in ids[j] if x==s],0.)
            append(((a,1) for a,(x,kids) in ids[i] if x[0] and kids[k][0]),q[j])
    C=np.zeros(offset[-1])
    root=[(a,s[1]) for a,(s,_) in ids[0]]
    for a,f in root:C[a]=target(f)
    return (coo_matrix((value,(row,col)),shape=(len(rhs),offset[-1])).tocsr(),
            rhs,C,root,ids,ch)

def optimize(par,mask,p,q,target,want_max=True,calibrate=None,compact=True):
    fn=factored if compact else full
    data=fn(par,mask,p,q,target)
    A,b,c,root=data[:4]
    if not compact:
        A=np.asarray(A)
        root=list(enumerate(root))
    if calibrate is not None:
        from scipy.sparse import vstack, csr_matrix
        e=np.zeros(len(c))
        for i,r in root:e[i]=bool(r&1)
        A=vstack([csr_matrix(A),csr_matrix(e.reshape(1,-1))])
        b=b+[calibrate]
    v=linprog(-np.array(c) if want_max else c,A_eq=A,b_eq=b,method="highs")
    assert v.success,v.message
    optimum=float(np.array(c)@v.x)
    if compact and len(par)<=9:
        check_lift(par,mask,p,q,target,data[4],data[5],v.x,optimum,calibrate)
    return optimum,len(c)

def check_lift(par,mask,p,q,target,ids,ch,sol,claimed,calib):
    own=[]
    local=[]
    for group in ids:
        tab={k:sol[j] for j,k in group}
        base=defaultdict(float)
        for (s,_),w in tab.items():base[s]+=w
        local.append(tab);own.append(base)
    total=score=seen=0.
    one=[0.]*len(par);two=[0.]*len(par)
    for vector in product((0,1),repeat=len(par)):
        state=[None]*len(par)
        keys=[None]*len(par)
        for j in reversed(range(len(par))):
            kids=tuple(state[k] for k in ch[j])
            tag=mask[j] if vector[j] else 0
            for x,v in kids:tag|=v
            state[j]=vector[j],tag
            keys[j]=state[j],kids
        w=local[0][keys[0]]
        if w>0.:
            for j in range(1,len(par)):
                b=own[j][state[j]]
                if b<1e-14:
                    w=0.;break
                w*=local[j][keys[j]]/b
        total+=w
        for j,u in enumerate(vector):
            one[j]+=w*u
            if j:two[j]+=w*u*vector[par[j]]
        score+=w*target(state[0][1])
        seen+=w*bool(state[0][1]&1)
    assert abs(total-1)<1e-8 and abs(score-claimed)<1e-8
    assert np.allclose(one,p,atol=1e-8) and np.allclose(two[1:],q[1:],atol=1e-8)
    if calib is not None:assert abs(seen-calib)<1e-8

def solve_demo():
    pa=(None,0,0,0,0)
    # The fifth mask bit is not needed: 1=alarm, 2,4=old and
    # activated failure OR, 8=optional-only risk, statutory extra.
    mask=(0,6,12,1,1)
    p=(.5,)+(.25,)*4
    q=(None,)+(.125,)*4
    def get(a,b=0.,high=True):
        return optimize(pa,mask,p,q,lambda x:margin(x,a,b),high,.5)[0]
    v=[get("global",high=False),get("global"),get("quiet_joint"),
          get("seen_joint"),get("seen_cond",.5),get("new_only")]
    assert np.allclose(v,[.25,.5,.25,.5,.25,.25],atol=1e-9)
    # Explicit finite whole laws at both global extrema and each cohort
    # competitor. The fair connector bit is independent of these atoms.
    atoms=[
        [(1,0,1,0),(0,0,0,1),(0,1,0,0),(0,0,0,0)],
        [(1,0,1,0),(0,1,0,1),(0,0,0,0),(0,0,0,0)],
        [(0,1,1,0),(0,0,0,1),(1,0,0,0),(0,0,0,0)]]
    assert [[sum(row[i] for row in w) for i in range(4)] for w in atoms]==[[1]*4]*3
    def exact(w,arm):
        if arm==0:return sum(x or (y and (d or e)) for x,y,d,e in w)/4
        return sum(x and not (d or e) for x,y,d,e in w)/4
    assert [exact(w,0) for w in atoms]==[.25,.5,.5] and exact(atoms[-1],1)==.25
    # Hidden nonconsumed connector imposes equality across both
    # kept vertices. Treating the induced subgraph as the input loses it.
    stop=optimize((None,0,1),(6,0,6),(.25,)*3,(None,.25,.25),
                  lambda x:margin(x))[0]
    assert abs(stop-.25)<1e-9
    assert abs(optimize((None,0),(6,6),(.25,)*2,(None,0),
                  lambda x:margin(x))[0]-.5)<1e-9
    return [round(x,8) for x in v],stop

def main():
    d,connector=solve_demo()
    rng=Random(6508)
    count=0;many=[]
    for n in (3,4,6,8,9):
      for k in range(8):
        pa=(None,)+tuple((i-1)//2 for i in range(1,n))
        # Generate consistent data, not necessarily tree-Markov.
        observations=[[rng.randrange(2) for _ in range(n)] for j in range(24)]
        p=[sum(x[i] for x in observations)/24 for i in range(n)]
        q=[None]+[sum(x[i]*x[pa[i]] for x in observations)/24 for i in range(1,n)]
        mask=[rng.randrange(16) for _ in range(n)]
        for a,eps in (("global",0.),("quiet_cond",.25),("seen_cond",.25),("new_only",0.)):
          for high in (False,True):
            f=lambda x:margin(x,a,eps)
            f1,_=optimize(pa,mask,p,q,f,high)
            f2,_=optimize(pa,mask,p,q,f,high,compact=False)
            assert abs(f1-f2)<1e-8,(n,k,f1,f2)
            count+=1
    for n in (31,63,127):
        pa=(None,)+tuple((i-1)//2 for i in range(1,n))
        mask=[(1<<(i%4))|2 for i in range(n)]
        p=(.02,)*n
        q=(None,)+(.015,)*(n-1)
        x,h=optimize(pa,mask,p,q,lambda f:margin(f))
        many.append([n,h,round(x,8)])
    print(json.dumps(dict(compact_vs_full=count,example=d,hidden_connector=connector,
                          larger_factor_cases=many),indent=2,sort_keys=True))
if __name__=="__main__":main()
