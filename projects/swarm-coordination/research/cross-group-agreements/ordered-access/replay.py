"""Toy warehouse agreement: event execution and independent blocking-deviation scan."""
from itertools import combinations, product
import json

def profile(b,c,lag,deadline):
    if not b: return None
    return min((t+1 for t in c if t >= min(b)+lag and t+1 <= deadline), default=None)

def gains(end,pay):
    b,c,l,m,k=pay
    return b-l*end,c-m*end

def coalitional_block(end,pay):
    if end is None: return False
    x,y=gains(end,pay); k=pay[-1]
    return max(-k,1-x)<=min(k,y-1)

def repair(b,c,lag,deadline,pay):
    end=profile(b,c,lag,deadline)
    if not coalitional_block(end,pay): return None
    x,y=gains(end,pay)
    return min(b),end-1,max(-pay[-1],1-x)

def exact_deviations(b,c,lag,deadline,pay):
    """Enumerate physical start choices and all possible binding transfers."""
    good=[]
    for s,t,q in product(b,c,range(-pay[-1],pay[-1]+1)):
        if t-s < lag or t+1 > deadline: continue
        u,v=gains(t+1,pay)
        good.append((s,t,q,u+q,v-q))
    return good

def settle(b,c,lag,deadline,pay,plan):
    """Transition system: a cut, irrevocable independent old job, then ordered dock use."""
    tr=[(-1,"old-job-admitted","A"),(0,"old-job-start","A"),
        (0,"optional-access-register","B",list(b)),(0,"optional-access-register","C",list(c)),
        (0,"public-decision",bool(plan))]
    if plan is not None:
        tr.append((0,"bilateral-conditional-acceptance", list(plan)))
    holder="A"; due=1; stock="B"; us=[0,0,0]
    if plan is not None:
        s,t,q=plan
        assert -pay[-1] <= q <= pay[-1]
    for tick in range(1,deadline+1):
        if holder is not None and tick==due:
            tr.append((tick,"physical-release",holder))
            if holder=="A": us[0]=7
            if holder=="B": stock="dock"
            if holder=="C":
                assert stock=="dock"
                stock="C"
                x,y=gains(tick,pay); us[1:]=[x+q,y-q]
                tr.append((tick,"paired-completion",list(us)))
            holder=None
        if plan is not None and tick in (s,t):
            assert holder is None
            if tick==s:
                assert tick in b and stock=="B"
                holder="B"
            else:
                assert tick in c and stock=="dock" and tick-s>=lag
                holder="C"
            due=tick+1
            tr.append((tick,"optional-dock-start",holder))
    assert holder is None and us[0]==7
    return dict(trace=tr,utility=us,end_stock=stock)

def main():
    slots=range(1,5); ss=[s for n in range(5) for s in combinations(slots,n)]
    specs=list(product((0,2,5),(0,2,5),(0,1),(0,1),(0,1,3)))
    physical=tests=blocks=execution_cases=0
    for b,c,h,D in product(ss,ss,(1,2,3),range(2,6)):
        direct=min((j+1 for i in b for j in c if j-i>=h and j+1<=D),default=None)
        assert direct==profile(b,c,h,D); physical+=1
        for s,t in product(b,c):
            if t-s >= h and t+1 <= D:
                run=settle(b,c,h,D,(20,20,1,1,0),(s,t,0))
                assert run['utility']==[7,20-(t+1),20-(t+1)]
                assert run['end_stock']=='C'
                execution_cases+=1
        for p in specs:
            ds=exact_deviations(b,c,h,D,p)
            result=repair(b,c,h,D,p)
            improves=[d for d in ds if d[3]>0 and d[4]>0]
            assert bool(improves)==bool(result)
            if result:
                blocks+=1
                chosen=next(d for d in ds if d[:3]==result)
                assert chosen in improves
                # Grand/ A-containing coalition cannot give A a strict gain.
                # No singleton can profitably produce a pair or abandon this outcome.
                assert not any(d[3]>chosen[3] and d[4]>chosen[4] for d in ds)
            tests+=1
    p=(6,5,1,1,2); a=((1,),(2,)); b=((2,),(1,))
    featured={k:settle(*rights,1,4,p,plan) for k,rights,plan in [
        ('prior-agreement-upon-forward-rights',a,None),
        ('prior-agreement-upon-reverse-rights',b,None),
        ('stable-repair-forward',a,repair(*a,1,4,p)),
        ('stable-repair-reverse',b,repair(*b,1,4,p)),
    ]}
    assert featured['prior-agreement-upon-forward-rights']['utility']==featured['prior-agreement-upon-reverse-rights']['utility']==[7,0,0]
    assert featured['stable-repair-forward']['utility']==[7,1,4]
    assert featured['stable-repair-reverse']['utility']==[7,0,0]
    print(json.dumps(dict(physical_cases=physical,execution_cases=execution_cases,utility_cases=tests,strict_blocks=blocks,witnesses=featured),indent=1,sort_keys=True))
if __name__=='__main__': main()
