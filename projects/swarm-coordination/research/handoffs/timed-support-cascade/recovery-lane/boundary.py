"""Authored comparison against the exact #356 receiver factors, not a held-out."""
from itertools import product
from types import FunctionType
import json
import replay as r
p = r.exact('frozen_interface.py','5daeb3143114d8c7478165fca480bc10331fe3f88bc70de7f6d09a9535061dfc')
a=p.index('PRIMARY = ')
b=p.index('TOKEN=')
env={'__name__':'boundary_interface','__file__':__file__}
exec(compile(p[:a]+p[b:],'frozen_interface.py','exec'),env)
frames=env['frames']

def instantiate(simulate,variant):
    f=FunctionType(frames.__code__,dict(frames.__globals__,simulate=simulate))
    out=[]
    for base in product((1,2),(False,),(4,5,6)):
        out.extend(f(base,variant))
    return out

def ext(early):
    def run(live,h,d,early2,before,D):
        assert early2==early and not d
        return r.simulate(live,True,True,early,True,D)
    return run

def primary_hop(live,h,d,early,before,D):
    return r.primary(live,True,False,False,True,D)

def check(src,ordinary,both):
    idx=[{r[d][0]:r[d] for r in ordinary} for d in range(3)]
    S=[[r[d] for r in src] for d in range(3)]
    M=[{w:idx[d][w[0]] for w in S[d]} for d in range(3)]
    assert all(len(m)==len(src) for m in M)
    for d,m in enumerate(M):
        assert {w[:2] for w in m.values()}=={r[d][:2] for r in ordinary+both}
    failing={}
    counts={}
    for name,scope,test in env['FACTORS']:
        F=0
        N=0
        for row in product(*(S[d] for d in scope)):
            N+=1
            F+= test(*row)!=test(*(M[d][w] for d,w in zip(scope,row)))
        failing[name]=F
        counts[name]=N
    return dict(factors=counts,mismatches=failing,phase_mismatches=sum(a[3:]!=b[3:] for a,b in zip(src,ordinary)))

def main():
    s=instantiate(ext(True),'early-onset')
    a=instantiate(r.primary,'ordinary-a')
    b=instantiate(r.primary,'ordinary-b')
    passed=check(s,a,b)
    assert not any(passed['mismatches'].values()) and not passed['phase_mismatches']
    x=instantiate(ext(False),'ordinary-a')
    y=instantiate(primary_hop,'ordinary-a')
    z=instantiate(primary_hop,'ordinary-b')
    rejected=check(x,y,z)
    assert rejected['mismatches']['authority']==0 and rejected['mismatches']['physical']>0
    assert rejected['phase_mismatches']>0
    # Key is (long, no terminal slow dwell, deadline 5, tick 4).
    key=(2,False,5,4)
    physical=lambda rows: next(a[1] for _,a,_,_,_ in rows if a[0]==key)
    print(json.dumps(dict(scope='authored second workload; original undelayed-dwell subcarrier only',positive=passed,negative=rejected,physical_tick4=[physical(x),physical(y)]),sort_keys=True,indent=1))
if __name__=='__main__':main()
