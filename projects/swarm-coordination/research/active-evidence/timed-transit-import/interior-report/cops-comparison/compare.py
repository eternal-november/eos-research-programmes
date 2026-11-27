"""Compare #685 event rule with unchanged pinned COPS flow on per-law paths."""
import argparse
import json
from itertools import product
import sys
from pathlib import Path
from bridge import FixtureGraph, initialize, scoped_solver

def call(COPS,Constr,w,D,E,s,bg,cap,mode):
    d,l,u=w
    # Expand the permitted committed sequence into explicit position cuts.
    start='entry'
    path=['entry']*s+['entry']+['rail']*(d-1)+['portal','bend','near','exit']
    move_at=D+1
    H=max(D+2,E)
    path=(path+['exit']*(H+1))[:H+1]
    contact_time=s+d+(3 if mode=='exit' else 0)
    a='exit' if mode=='exit' else 'portal'
    can_send=(l<=contact_time<u and
              (bg if contact_time<=4 else 0)+3<=cap)
    moves=(('entry','rail'),('rail','portal'),('entry','portal'),
           ('portal','bend'),('bend','near'),('near','exit'),
           ('ready','goal'))
    links=((a,'ready'),)
    graph=FixtureGraph(moves,links,{'carrier':start,'worker':'ready'})
    requirements=[('carrier',t,(pos,)) for t,pos in enumerate(path)]
    requirements += [('carrier',E,('exit',))]
    requirements += [('worker',t,('ready',) if t<=move_at else ('goal',))
                      for t in range(H+1)]
    erased=tuple((t,a,'ready') for t in range(H+1)
                 if t!=contact_time or not can_send)
    late=tuple((t,a,'ready') for t in range(D+1,H+1))
    cls=scoped_solver(COPS,Constr,requirements,erased,late)
    c=cls(graph=graph,master=['carrier'],static_agents=[],src=['carrier'],
          snk=['worker'],always_src=True)
    c.T=H
    sol=c.solve_flow(master=True,connectivity=True,frontier_reward=False,cut=False)
    if sol['status']=='infeasible':return False
    assert sol['status']=='optimal'
    assert c.traj['carrier',E]=='exit' and c.traj['worker',D+2]=='goal'
    return True

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('up')
    ap.add_argument('parent')
    a=ap.parse_args()
    # Only the checked exact launch formula is imported from #685.
    sys.path.insert(0,str(Path(a.parent).resolve()))
    from replay import projected
    cops, con=initialize(a.up)
    sets=(((1,1,2),(2,2,3)),((1,2,3),(2,1,2)))
    suite=[(w,2,5,s,0,6,mode) for W in sets for w in W
            for s in range(3) for mode in ('interior','exit')]
    suite+= [((1,4,6),5,8,s,b,5,'interior') for s,b in product((3,4),(0,3))]
    suite+= [((2,2,3),D,E,0,0,6,'interior') for D,E in product((1,2),(4,5))]
    checks=[]
    for w,D,E,s,bg,cap,mode in suite:
        point=call(cops,con,w,D,E,s,bg,cap,mode)
        assert point==(s in projected(w,(D,E),cap,bg,mode)),(w,D,E,s,bg,cap,mode,point)
        checks.append(dict(world=w, deadlines=(D,E), launch=s, old_debit=bg,
                           capacity=cap, mode=mode, native_feasible=point))
    print(json.dumps(dict(conditions=len(checks),feasible=sum(x['native_feasible'] for x in checks),
                          cases=checks),indent=2,sort_keys=True))
if __name__=='__main__':main()
