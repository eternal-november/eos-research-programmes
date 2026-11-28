from decimal import Decimal as D
from itertools import product
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from egress import Map,load_scene,verify,GATE_A,GATE_B,clipped
from timeline import BRANCH,load,box,minimum_temporal_gap,schedule,duration
from pathlib import Path
import json,sys
P=HERE.parent

def t_edge(a,b):
    ell=sum(D(x-y)**2 for x,y in zip(a,b)).sqrt()
    return 2*ell.sqrt() if ell<=9 else ell/3+3

def gate_open(a,b,g):
    return not clipped([a,b],g)

def chords(M,p,g):
    best=[D(0)]+[D('Infinity')]*(len(p)-1)
    parent={0:None}
    for j in range(1,len(p)):
        for i in range(j):
            cost=t_edge(p[i],p[j])
            if best[i]+cost>=best[j] or not gate_open(p[i],p[j],g):continue
            if not M.clear(*sorted([p[i],p[j]])):continue
            best[j]=best[i]+cost
            parent[j]=i
    out=[]
    k=len(p)-1
    while k is not None:
        out.append(p[k]);k=parent[k]
    out.reverse()
    assert out[0]==p[0] and out[-1]==p[-1]
    for a,b in zip(out,out[1:]):
        assert gate_open(a,b,g) and M.certificate(a,b)>0
    assert sum(t_edge(a,b) for a,b in zip(out,out[1:]))==best[-1]
    return out

def at(p,t):
    run=[]
    for a,b in zip(p,p[1:]):
        u=t+t_edge(a,b)
        run.append((t,u,box(a,b)));t=u
    return run,t
def calculate():
    verify()
    T,F,pos=load_scene();m=Map(T,F)
    I=load('installer');I=I[:-2]+[(0,3,I[-3][2]),(0,3,6)]
    # Same probe as the original policy, so knowledge for egress is
    # available at the same time even though the courier starts early.
    it,j=schedule(I,D(14))
    it=[(D(0),D(14),box((100,50,8),(100,60,8)))]+it+[(j,D(200),box(I[-1],I[-1]))]
    b=BRANCH['far']
    bt,q=schedule(b,D(0));q0=q+D('.5')
    assert q0<35
    res={}
    paths={key:chords(m,load(key),gate) for key,gate in
        [('far_short',GATE_B),('far_detour',GATE_A),('near',GATE_A)]}
    for key in ('far_short','far_detour'):
        r=paths[key]
        for i in range(601):
            wait=D(i)/10
            walk,done=at(r,q0+wait)
            ts=bt+[(q,q0+wait,box(b[-1],b[-1]))]+walk
            if done>200:continue
            ts+=[(done,D(200),box(r[-1],r[-1]))]
            if minimum_temporal_gap(it,ts)>D('.25'):
                res[key]={"path":r,"wait":str(wait),"start_egress":str(q0+wait),
                    "motion":str(round(done-q0-wait,6)),"finish":str(round(done,6)),"legs":len(r)-1}
                break
        print(key,'not found' if key not in res else res[key]['finish'], 'legs',len(r)-1,flush=True)
    def time(p):
        return sum(t_edge(a,b) for a,b in zip(p,p[1:]))
    # Match the augmented egress repertoire in both arms while retaining
    # the two frozen initial approach macros, only still at their endpoints
    # can a continuation start (already generous eager knowledge after).
    F,N=duration(BRANCH['far']),duration(BRANCH['near'])
    no_comm_near=2*N+F+time(paths['far_short'])
    no_comm_far=min(F+time(paths['far_detour']),2*F+N+time(paths['near']))
    for key,arm in [('far_short','far'),('near','near')]:
        b=BRANCH[arm];bt,q=schedule(b,D(5));q0=q+D('.5')
        bt=[(D(0),D(5),box(b[0],b[0]))]+bt
        r=paths[key]
        for i in range(601):
            wait=D(i)/10
            walk,done=at(r,q0+wait)
            if done>D('167.5'):continue
            ts=bt+[(q,q0+wait,box(b[-1],b[-1]))]+walk+[(done,D(200),box(r[-1],r[-1]))]
            if minimum_temporal_gap(it,ts)>D('.25'):
                res['adaptive-'+arm]={"path":r,"wait":str(wait),"finish":str(round(done,6))}
                break
    print('relaxed fixed 6/42 egress bounds with chords and reversals',
          round(no_comm_near,6),round(no_comm_far,6),flush=True)
    print('adaptive-chord matched',[(s,res[s]['finish']) for s in res if s.startswith('adaptive')],flush=True)
    assert no_comm_near>D('167.5') and no_comm_far>D('167.5')
    assert len(res)==4
    return res

if __name__=='__main__':
    d=calculate()
    (HERE/'chord-results.json').write_text(json.dumps(d,indent=2)+'\n')
