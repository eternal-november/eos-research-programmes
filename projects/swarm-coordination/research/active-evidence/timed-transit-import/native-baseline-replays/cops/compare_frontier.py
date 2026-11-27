"""Pinned COPS motion leaves for the same obligations as #727 (staged after reset)."""
from pathlib import Path
from itertools import product
from collections import deque
import json
import numpy as np
from scipy import sparse
from bridge import FixtureGraph, initialize
from mission import inputs, State, W, transition, actions, known, synth, replay_policy
from mission import START, SCOUT, GATE, DOCK, EXIT
ROOT=Path(__file__).resolve().parent
COPS,Constraint=initialize(ROOT)
NODES={0,1,2,3,4,6,8,9,13,16,39,42,43}
desk=((43,False),(39,False),(39,False))
inspect=((43,False),(1,False),(1,True),(43,True),(39,True),(39,True))
PROFILES={"free":(), "desk":desk, "inspect":inspect,
          "early":((43,False),(39,False),(2,False),(3,False)),
          "desk-abs":desk+((43,False),(1,False))+tuple((p,True) for p in (1,13,42,16,6,8,3)),
          "inspect-abs":inspect+tuple((p,True) for p in (43,1,13,42,16,6,8,3))}
def projection(g):
    outside=set(g)-NODES
    while outside:
        root=next(iter(outside));outside.remove(root)
        q=deque([root]);contacts=set()
        while q:
            x=q.popleft()
            contacts.update(v for v in g[x] if v in NODES)
            for v in g[x]:
                if v in outside:outside.remove(v);q.append(v)
        assert len(contacts)<=1 and not (contacts & set(GATE)),contacts
    return {v:tuple(sorted(set(g[v])&NODES)) for v in NODES}

def matches(profile,t,pos,inspected):
    prefix=PROFILES[profile]
    return t>=len(prefix) or (pos,inspected)==prefix[t]

def native(g,paid,closed,report_due,inspect_due,horizon,profile):
    initial=(START,int(paid)*2,False)
    states=list(product(sorted(g),range(3),(False,True)))
    moves=[]
    for p,carry,inspected in states:
        s=(p,carry,inspected)
        moves.extend((s,(n,carry,inspected)) for n in g[p])
        if p==SCOUT and carry==0:moves.append((s,(p,1,inspected)))
        if p==DOCK and carry==1:moves.append((s,(p,2,inspected)))
        if p==1 and not inspected:moves.append((s,(p,carry,True)))
    gg=FixtureGraph(tuple(moves),(),{"r":initial})
    class Scoped(COPS):
        def _solve(self,obj,constraint,**kw):
            idx=[];vals=[]
            def equal(cols,v):
                idx.extend([len(vals),c] for c in cols)
                vals.append(v)
            def occupy(t,f):
                equal([self.get_z_idx("r",s,t) for s in states if f(s)],1)
            for t,(pos,ins) in enumerate(PROFILES[profile]):
                if t>horizon:return {"status":"infeasible"}
                occupy(t,lambda s:s[0]==pos and s[2]==ins)
            occupy(min(report_due,horizon),lambda s:s[1]==2)
            occupy(min(inspect_due,horizon),lambda s:s[2])
            occupy(horizon,lambda s:s[0]==EXIT)
            if closed:
                for t in range(3,horizon):
                    equal([self.get_xf_idx("r",a,b,t) for a,b in moves
                         if tuple(sorted((a[0],b[0])))==GATE],0)
            aa,bb=zip(*idx) if idx else ((),())
            eq=sparse.coo_matrix((np.ones(len(idx)),(aa,bb)),shape=(len(vals),len(obj)))
            return super()._solve(obj,constraint & Constraint(A_eq=eq,b_eq=np.asarray(vals)),**kw)
    p=Scoped(graph=gg,master=["r"])
    p.T=horizon
    solution=p.solve_flow(master=False,connectivity=False,frontier_reward=False,cut=False)
    if solution["status"]=="infeasible":return False
    assert solution["status"]=="optimal"
    path=[p.traj[("r",t)] for t in range(horizon+1)]
    assert path[0]==initial and path[-1][0]==EXIT
    assert path[min(report_due,horizon)][1]==2 and path[min(inspect_due,horizon)][2]
    assert all(matches(profile,t,s[0],s[2]) for t,s in enumerate(path))
    for t,(a,b) in enumerate(zip(path,path[1:])):
        assert a==b or (a,b) in moves
        assert not(closed and t>=3 and tuple(sorted((a[0],b[0])))==GATE)
    return path

def reachable(g,paid,closed,r,i,h,profile):
    w=W(paid,closed,0)
    fringe={State(deposited=paid)}
    for t in range(h+1):
        fringe={z for z in fringe if matches(profile,t,z.pos,z.inspected)}
        if t==h:return any(z.pos==EXIT and z.deposited and z.inspected for z in fringe)
        fringe={transition(g,z,a,w,3,1,r,i) for z in fringe
                for a in actions(g,z,known(z,w,3),"none",1,r,i)}
    return False

def main():
    full,_,_=inputs();g=projection(full);out={}
    for paid,closed,profile,(r,h) in product((False,True),(False,True),("free","desk","inspect","early"),
                                  ((14,17),(20,24),(21,24),(23,26),(23,10),(23,8))):
        got=native(g,paid,closed,r,12,h,profile)
        assert bool(got)==reachable(full,paid,closed,r,12,h,profile),(paid,closed,profile,r,h)
        out[f"{int(paid)}/{int(closed)}/{profile}/{r}/{h}"]=bool(got)
    assert out["0/1/early/14/17"] and not out["0/1/desk/20/24"] and out["0/1/desk/21/24"]
    assert not out["0/1/inspect/21/24"] and out["0/1/inspect/23/26"]
    assert out["1/1/inspect/23/8"] and not out["1/1/desk/23/8"] and out["1/1/desk/23/10"]
    worlds=tuple(W(p,c,0) for p,c in product((False,True),repeat=2))
    vals={}
    for r,h,f in ((20,24,10),(21,24,10),(21,24,8),(22,26,8),(23,26,8)):
        ok,m,_=synth(full,worlds,"sealed",3,1,r,12,h,True,f)
        vals[f"{r}/{h}/{f}"]=ok
        if ok:replay_policy(full,worlds,"sealed",3,1,r,12,h,True,m,fast_egress=f)
    assert list(vals.values())==[False,True,False,False,True]
    staged={}
    for front,r,h,f in (("desk",21,24,10),("inspect",23,26,8)):
        p=native(g,True,False,r,12,f,front)
        assert p and all(tuple(sorted((u[0],v[0])))!=GATE for u,v in zip(p,p[1:]))
        leaves=[native(g,False,c,r,12,h,front+"-abs") for c in (False,True)]
        k=len(PROFILES[front+"-abs"])-1
        assert all(leaves) and leaves[0][:k+1]==leaves[1][:k+1] and leaves[0][k][0]==SCOUT
        staged[front]=[k, [p[0] for p in leaves[0][:k+1]],f]
    print(json.dumps({"native_cops_leaves":len(out),"vertices":[len(full),len(g)],
                     "causal_checks":vals,"staged_prefix_audit":staged,"records":out},sort_keys=True))
if __name__=="__main__":main()
