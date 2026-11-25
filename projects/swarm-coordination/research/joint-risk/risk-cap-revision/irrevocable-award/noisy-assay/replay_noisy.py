"""Parametric actual completion trade-off; same information raw policy support."""
from fractions import Fraction as Q
from itertools import product
from hashlib import sha256
from pathlib import Path
import importlib.util,json,sys

def load(path):
    spec=importlib.util.spec_from_file_location("pinned_award_replay",path)
    base=importlib.util.module_from_spec(spec);sys.modules[spec.name]=base
    spec.loader.exec_module(base)
    return base

def points(c,eps,audit):
    # (worst risk, completed work); the extrema here attain the same
    # pair under both laws after symmetrizing the coarse-signal policy.
    rs=[(Q(0),1+c),(Q(1,4),Q(7,4)),(Q(1,2),Q(3,2)+c)]
    if audit:rs += [(Q(0),Q(1)),(eps/2,Q(3,2)-eps/2),
                    ((1-eps)/2,1+eps/2),(Q(1,2),Q(3,2))]
    return rs

def frontier(c,eps,cap,audit):
    rs=points(c,eps,audit)
    opts=[w for x,w in rs if x<=cap]
    for (x,q),(y,w) in product(rs,repeat=2):
        if x<cap<y:opts.append(q+(w-q)*(cap-x)/(y-x))
    return max(opts)

def raw(base,c,eps,cap,audit):
    hs,laws=base.source(1)
    p=[[v*q for v in law for q in (1-eps,eps)] for law in laws]
    worlds=[(h,error) for h in hs for error in (0,1)]
    solver=base.LP([],[],[],[]); effects=[[{} for _ in worlds] for _ in range(2)]
    for a in ('early','hold','audit') if audit else ('early','hold'):
        def obs(h,e):return (h[1],h[-1]^e if a=='audit' else None)
        cells=sorted(set(obs(h,e) for h,e in worlds))
        for commands in product(base.options(a),repeat=len(cells)):
            j=solver.var((a,commands),0,1); acts=dict(zip(cells,commands))
            for i,(h,e) in enumerate(worlds):
                risk,_,work=base.scores(h,a,acts[obs(h,e)],False)
                effects[0][i][j]=risk
                effects[1][i][j]=work+(c-Q(1,4) if a=='hold' else 0)
    solver.equals({i:1 for i in range(len(solver.names))},1)
    util=solver.var('work',0,5)
    base.guarantee_endpoints(solver,effects[0],p,1,cap)
    base.guarantee_endpoints(solver,effects[1],p,-1,0,util)
    return solver.solve({util:1})[0]

def verify(base):
    k=0
    C=list(map(Q,['0','1/8','1/4','3/8','1/2','3/4']))
    E=list(map(Q,['0','1/20','1/12','1/6','1/5','1/4','1/2']))
    B=list(map(Q,['0','1/40','1/10','1/8','1/4','2/5','1/2']))
    for c,e,a in product(C,E,(False,True)):
        for cap in B:
            assert raw(base,c,e,cap,a)==frontier(c,e,cap,a)
            k+=1
    thresholds={}
    for c in C:
        x=(Q(1,2)-c)/(2*(1-c)) if c<Q(1,2) else 0
        thresholds[str(c)]=str(x)
        for e in E:
            # For epsilon<=1/2 only audit-on-safe can improve the frontier.
            assert (frontier(c,e,e/2,True)>frontier(c,e,e/2,False))==(c<Q(1,2) and e<x)
    chosen={str(e):str(frontier(Q(1,4),e,Q(1,8),True)) for e in E}
    assert chosen['0']=='13/8' and chosen['1/6']=='3/2'
    assert frontier(Q(1,4),ZERO,Q(1,8),False)==Q(3,2)
    return dict(raw_checks=k,symmetry_thresholds=thresholds,utility_at_one_eighth_cap=chosen)
ZERO=Q(0)
if __name__=='__main__':
    out=json.dumps(verify(load(Path(sys.argv[1]))),sort_keys=True,indent=2)+'\n'
    if len(sys.argv)>2:Path(sys.argv[2]).write_text(out)
    else:print(out,end='')
