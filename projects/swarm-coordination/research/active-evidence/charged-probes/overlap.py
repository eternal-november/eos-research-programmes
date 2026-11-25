"""Event-timed physical interference vs a certified independent port."""
from charged import Source, SHARED, SEPARATE
from functools import cache
from itertools import product

def feasible(z,E,L,independent,trace=False):
    d,s,c=z.cooldown,z.spare_dur,z.battery_cost
    chosen={}
    @cache
    def go(t,clean,k,B):
        # Any previous cleanup is an actual owed service, even if the
        # second crew gets a valid bit earlier. Both horizons are fixed.
        if clean>L or t>=E:return False
        for act in (SHARED,SEPARATE):
            if act==SHARED:
                if k and not z.guard:continue
                start=max(t,clean);end=start+1;spent=0
            else:
                if B<c:continue
                start=t if independent else max(t,clean)
                end=start+s;spent=c
            if end>E:continue
            if not k:
                chosen[t,clean,k,B]=(act,start,end,clean)
                return True
            after=end+d if act==SHARED and d else clean
            # Success at this attempt is feasible (same earlier deadlines).
            # Continue the maximal erasure prefix to test the worst law.
            if go(end,after,k-1,B-spent):
                chosen[t,clean,k,B]=(act,start,end,after)
                return True
        return False
    good=go(0,0,z.max_erased,z.battery)
    if not good or not trace:return good
    state=(0,0,z.max_erased,z.battery)
    route=[]
    while True:
        act,start,end,after=chosen[state]
        route.append((act,start,end,after))
        t,clean,k,B=state
        if not k:return route
        state=(end,after,k-1,B-(c if act==SEPARATE else 0))

def literal_one_schedule(z,plan,E,L,independent):
    t=0;physical_cleanup=[];budget=z.battery
    # Eager schedules attain the earliest times componentwise; independently
    # simulate actual occupancy rather than copying the recurrence.
    for i,act in enumerate(plan):
        pending=i+1<len(plan)
        if act==SEPARATE:
            budget-=z.battery_cost
            if budget<0:return False
        if act==SHARED:
            if pending and not z.guard:return False
        duration=1 if act==SHARED else z.spare_dur
        while (act==SHARED or not independent) and (
              any(k in physical_cleanup for k in range(t,t+duration))):
            t+=1
        # After transfer failed physical cleanup exists even when no pilot
        # returned. The standby guard works until the actual final step.
        t+=duration
        if pending and act==SHARED:
            physical_cleanup+=list(range(t,t+z.cooldown))
    return t<=E and all(k<L for k in physical_cleanup)

def run():
    n=0
    for D,s,c,g,k,B,slack,ind in product(
        range(4),range(1,4),range(1,3),(False,True),range(5),range(5),
        [(3,3),(5,3),(5,6),(7,7),(10,10)],(False,True)):
        z=Source(D,s,c,g,k,B);E,L=slack
        a=feasible(z,E,L,ind)
        b=any(literal_one_schedule(z,p,E,L,ind) for p in
              product((SHARED,SEPARATE),repeat=k+1))
        assert a==b,(z,slack,ind,a,b)
        n+=1
    print(n,"matched physical schedule enumeration checks")
    z=Source(3,2,1,True,2,1)
    assert feasible(z,5,4,True) and not feasible(z,4,4,True)
    assert not feasible(z,5,3,True)
    assert not feasible(z,6,6,False) and feasible(z,7,6,False)
    a=feasible(z,5,4,True,True)
    print("same charged sensing budgets: independent port E=5 / old cleanup L=4;",a)
    print("shared crew duty forbids that overlap; exact serial evidence deadline 7")
    # Earlier success can create timely new evidence before a different
    # duty has settled. It must not be used to erase that old requirement.
    assert a[0]==(SHARED,0,1,4) and a[1][0]==SEPARATE
    print("if isolated attempt succeeds on its first try, evidence at 3 still leaves old cleanup until 4")
if __name__=="__main__":run()
