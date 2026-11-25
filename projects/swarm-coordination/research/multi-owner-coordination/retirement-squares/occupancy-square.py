"""Atomic configuration amendment versus paid physical handoff."""
from dataclasses import dataclass,replace
from itertools import product
from signatures import Hold, observed

def path(lane,first,last,T,K):
    return tuple(int(i==lane and first<=t<last)
                 for i in range(K) for t in range(T))

@dataclass(frozen=True)
class Plan:
    lane_for_new: int
    holds: tuple

def amend(state,lane):
    return replace(state,lane_for_new=lane)

def accept(state,start,end,k,T):
    return replace(state,holds=state.holds+(Hold(0,path(state.lane_for_new,start,end,T,k),1),))

def one_old_new(t0,tbegin,tsettle,T,K,old,new):
    # The earlier transfer requires both lanes during the acquisition window.
    # Still counts the old physical use even though the new grant is recognized.
    a=path(old,t0,tsettle,T,K)
    b=path(new,tbegin,T,T,K)
    return tuple(x+y for x,y in zip(a,b))

def allowed(hold,lane,t,T):
    return hold[lane*T+t]==0

def consumer(hold,t,T,K):
    return tuple(hold[lane*T+s] for lane in range(K) for s in range(t,T))

def main():
    n=0
    for T,K in product(range(3,9),range(2,5)):
        for t0,begin,settle,old,new in product(range(T),range(T),range(T+1),range(K),range(K)):
            if not(t0<begin<settle<=T and old!=new):continue
            state=Plan(old,())
            earlier=amend(accept(state,t0,T,K,T),new)
            later=accept(amend(state,new),t0,T,K,T)
            before,after=observed(earlier.holds,K*T),observed(later.holds,K*T)
            assert not allowed(before,old,t0,T) and allowed(after,old,t0,T)
            actual=one_old_new(t0,begin,settle,T,K,old,new)
            for cutoff in range(T+1):
                # A device-specific authenticated physical drain at settle is
                # required to reuse the later boundary. No rewriting old history.
                assert (consumer(actual,cutoff,T,K)==consumer(after,cutoff,T,K))==(cutoff>=settle)
            assert actual[old*T+begin]+actual[new*T+begin]==2
            n+=1
    print(n,'live traces; paid migration compares only on and after actual settlement')
if __name__=='__main__':main()
