"""Latency/pace-aware bounded corridor reduction."""
from itertools import product
import json

def fit(a,b,P):
    l,r,x=a
    u,v,y=b
    return r!=u or P>=x+y

def relation(menus,P,D=None):
    d={(m,m):(m[2],(m,)) for m in menus[0] if m[2]<=P and (D is None or m[2]<=D)}
    for choices in menus[1:]:
        new={}
        for (a,m),(w,hist) in d.items():
            for b in choices:
                z=w+b[2]
                if b[2]<=P and (D is None or z<=D) and fit(m,b,P):
                    if (a,b) not in new or new[a,b][0]>z:
                        new[a,b]=(z,hist+(b,))
        d=new
    return d

def join(x,y,P,D=None):
    out={}
    for (a,u),(s,hs) in x.items():
        for (v,b),(t,ht) in y.items():
            w=s+t
            if fit(u,v,P) and (D is None or w<=D):
                if (a,b) not in out or out[a,b][0]>w:
                    out[a,b]=(w,hs+ht)
    return out

def feasible(a,P):
    # Four physical jobs, station port occupancy at their forced deadlines.
    # Independent of formula used by composition.
    occupancy={}
    for k in range(4):
        t=k*P
        for i,(x,y,g) in enumerate(a):
            for port in ((i,x),(i+1,y)):
                old=occupancy.setdefault(port,[])
                if any(s<t+g and t<e for s,e in old):
                    return False
                old.append((t,t+g))
            t+=g
    return True

def direct(menus,P):
    d={}
    for a in product(*menus):
        if feasible(a,P):
            end=a[0],a[-1]
            w=sum(x[2] for x in a)
            d[end]=min(d.get(end,w),w)
    return d

def weights(d):
    return {k:v[0] for k,v in d.items()}

def pareto(menus):
    # P above 2G is identical to 2G at this interface.
    G=max(x[2] for m in menus for x in m)
    fronts={}
    for P in range(1,2*G+1):
        for k,(cost,_) in relation(menus,P).items():
            f=fronts.setdefault(k,[])
            if not f or cost<f[-1][1]:
                f.append((P,cost))
    return fronts

def main():
    modes=((0,0,1),(1,0,2),(0,1,3))
    ms=[tuple(m for i,m in enumerate(modes) if b>>i&1) for b in range(1,8)]
    cases=joins=length_pairs=0
    for n,P in product(range(1,5),range(7)):
        for menus in product(ms,repeat=n):
            d=direct(menus,P)
            t=relation(menus,P)
            assert weights(t)==d
            assert all(feasible(a,P) and sum(x[2] for x in a)==w for w,a in t.values())
            for cap in (0,2,4,8,12):
                assert weights(relation(menus,P,cap))=={k:w for k,w in d.items() if w<=cap}
                for mid in range(1,n):
                    assert weights(join(relation(menus[:mid],P,cap),
                                        relation(menus[mid:],P,cap),P,cap))==weights(relation(menus,P,cap))
                    joins+=1
            cases+=1
    a=(0,0,3); b=(0,0,1); c=(1,1,2)
    front=pareto(((a,),(b,c),(a,)))
    assert front=={(a,a):[(3,8),(4,7)]}
    # Equal length, equal exposed modes and feasibility, all distinct
    # durations. Changing only the consuming deadline distinguishes them.
    endpoint=(0,1,1)
    for n in range(2,129):
        variants=[]
        for k in range(n-1):
            f=((endpoint,),)+(((0,1,2),),)*k+(((0,1,1),),)*(n-2-k)+((endpoint,),)
            t=relation(f,2)
            assert set(t)=={(endpoint,endpoint)}
            variants.append(t[endpoint,endpoint][0])
        assert variants==list(range(n,2*n-1))
        length_pairs+=len(variants)
    print(json.dumps(dict(physical_configuration_cases=cases,truncated_joins=joins,
                          distinct_equal_length_variants=length_pairs,
                          pace_latency=[[3,8],[4,7]]),sort_keys=True,indent=2))
if __name__=="__main__":main()
