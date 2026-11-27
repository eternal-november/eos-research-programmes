from pathlib import Path
from math import sin,cos,tan,atan
from itertools import product
import json,sys,subprocess
from scipy.optimize import linprog

EPS=1e-9
def theory(r,lo,hi,delta,hold):
    z=lo/cos(r) if hold is None else hold
    return lo-EPS<=z*cos(r) and z<=hi+EPS and z*sin(r)<=delta+EPS

def direct(r,lo,hi,d,hold):
    ar=[];rhs=[]
    for t in (-r,-r/2,0,r/2,r):
        c,s=cos(t),sin(t)
        ar.extend([(c,s),(-c,-s),(-s,c),(s,-c)])
        rhs.extend((d,d,hi,-lo))
    result=linprog([0,0],A_ub=ar,b_ub=rhs,
                   bounds=[(None,None),(hold,hold) if hold is not None else (None,None)],
                   method="highs")
    assert result.status in (0,2)
    return result.success

def source(up,candidates):
    inputtext=''.join(' '.join(map(str,entry))+'\n' for entry in candidates)
    gaz=Path(__file__).resolve().with_name('gaz.py')
    res=subprocess.run([sys.executable,'-B',gaz,up],input=inputtext,text=True,
                        capture_output=True,check=True)
    return [tuple(map(float,line.split())) for line in res.stdout.splitlines()]

def main(up):
    counts=0
    for r,lo,hi,d,hold in product((0.,.125,atan(.5),.7),(0.3,.6),(0.65,.70,1.0),
                                  (0.,.1,.31,.5),(None,.4,.625,.8)):
        assert theory(r,lo,hi,d,hold)==direct(r,lo,hi,d,hold),(r,lo,hi,d,hold)
        counts+=1
    r=atan(.5)
    choices={'full':(0,.6/cos(r)), 'carry':(0,.625),
             'fresh_plus':(-.625*tan(r),.625), 'endpoint_only':(0,.72)}
    names=['minus','center','plus']
    angles=(-r,0.,r)
    cases=[(*v,t) for v in choices.values() for t in angles]
    rows=source(up,cases)
    assert len(rows)==len(cases)
    for (x,z,t),(rx,rz) in zip(cases,rows):
        assert abs(rx-(x*cos(t)+z*sin(t)))<EPS
        assert abs(rz-(z*cos(t)-x*sin(t)))<EPS
    def good(u,d=.31):
        x,z=u
        return abs(x)<=d+EPS and .6-EPS<=z<=.7+EPS
    facts={}
    for i,k in enumerate(choices):
        g=rows[3*i:3*i+3]
        facts[k]={n:tuple(round(v,10) for v in u) for n,u in zip(names,g)}
        if k=='full':assert all(good(u) for u in g)
        elif k=='carry':assert not any(good(u) for u in (g[0],g[2]))
        elif k=='fresh_plus':assert good(g[2]) and not good(g[0])
        else:assert good(g[0],.35) and good(g[2],.35) and not good(g[1],.35)
    return dict(optimization_cases=counts,selected_setter=facts,frames=3)
if __name__=='__main__':print(json.dumps(main(Path(sys.argv[1]).resolve()),sort_keys=True))
