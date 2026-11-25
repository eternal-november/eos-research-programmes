"""Matched route-and-effect planner for the declared single-probe family."""
from source import *
from collections import defaultdict

def proxy(w,read,name):
    if read==3 and name=="loss" and not w.q_reports_fault:return -2
    return w.failed if name=="loss" and read else w.blocked if name=="exit" and read else -2

def first_step(path,w):
    for a,b in zip(path,path[1:]):
        if b not in adj(w,a):return False
    return True

def covers(K,route):
    # Entry into the one-way egress passage is allowed only if it actually
    # reaches base in all states in this control cell.
    return all(first_step([J,route,BASE],w) for w,stock,s in K)

def assignment(K):
    available=[set.intersection(*(set(stock[i]) - ({w.failed, s.held} |
                     ({1} if w.probe_disturbance and s.read==3 else set()))
                     for w,stock,s in K)) for i in range(2)]
    return next(((FORWARD,a,b) for a,b in product(*available) if a!=b),None)

def structured(W,H,B):
    for station,path in [(None,[J]),(P,[J,P]),(Q,[J,Q1,Q])]:
        if not all(first_step(path,w) for w in W):continue
        out=len(path)-1+int(station is not None)
        if 2+out+1+len(path)-1+2>H:continue
        initial=[(w,stock,s) for w in W for s,stock in [phase0(w)]]
        early=assignment(initial) if 3<=B else None
        if 2+out+1>B and early is None:continue
        groups=defaultdict(list)
        for w in W:
            s,stock=phase0(w)
            if station is not None:
                # P/Q are reached by observable adjacency; this fixture
                # requires one choice common to the entire initial cell.
                for a in path[1:]:s=effect(w,s,a,0,stock)
                if s.read:break
                s=effect(w,s,PROBE,0,stock)
            groups[observe(w,s)].append((w,stock,s))
        else:
            rule={}
            for obs,K in groups.items():
                forward=(assignment(K) if 2+out+1<=B else None) if early is None else early
                route=next((z for z in (L,R) if covers(K,z)),None)
                if forward is None or route is None:break
                rule[obs]=(forward,route)
            else:return station,("before probe" if early is not None else "after probe"),rule
    return None

def check():
    m=0
    for sf,openq,aux,only,stable in product(range(2),repeat=5):
        if sf:types=((L,-1),(R,-1))
        else:types=((L,0),(R,2))
        worlds=tuple(World(exit,loss,bool(openq),bool(aux),False,not only,not stable)
                     for exit,loss in types)
        for D,B in [(5,3),(7,5),(8,4),(8,5),(9,6),(10,5),(10,6),(11,9)]:
            struct=structured(worlds,D,B)
            whole=plan(worlds,D,B)
            assert (struct is not None)==bool(whole),(worlds,D,B,struct,whole)
            m+=1
    print(m,"matched exact whole policy versus factored source-window checks")
    for t in [4,5,6]:
        print("report deadline",t,"just in time egress by 10?", bool(
            structured((World(L,0),World(R,2)),10,t)))
if __name__=="__main__":check()
