"""Enumerate deadline-success masks from the existing native model."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
import json
from timed_reference import ACTION,worlds,update,perceive,TARGET,all_obs,make,first_output,freeze,native,A,D

def maximal(masks):
    return tuple(m for m in sorted(set(masks)) if not any(m!=z and m&z==m for z in masks))

@lru_cache(None)
def possible(S,remaining,t=0,arrival=99):
    # Mission success evaluated at this deadline, after deterministic causal feedback.
    here=sum(1<<i for i,s in S if s[:2]==TARGET)
    candidates={here}
    if not remaining:return tuple(candidates)
    clock=t+1
    for a in ACTION:
        branches=defaultdict(list)
        for i,s in S:
            t=update(s,a)
            branches[all_obs(clock,t,arrival,"bound")].append((i,t))
        sets=[possible(tuple(B),remaining-1,clock,arrival) for B in branches.values()]
        for row in product(*sets):
            candidates.add(sum(row)) # disjoint initial-state bit labels
    return maximal(candidates)

@lru_cache(None)
def feasible_only(S,t,limit,arrival):
    # Independent predicate: can all worlds in the selected sub-support
    # be served? This never builds success masks in its recursion.
    if all(s[:2]==TARGET for s in S):return True
    if t==limit:return False
    for a in ACTION:
        B=defaultdict(set)
        for s in S:
            u=update(s,a)
            B[all_obs(t+1,u,arrival,"bound")].add(u)
        if all(feasible_only(tuple(sorted(v)),t+1,limit,arrival) for v in B.values()):
            return True
    return False

def compare(S,front,limit,arrival):
    exact=0
    for mask in range(16):
        chosen=tuple(sorted(s for i,s in S if (1<<i)&mask))
        want=any((a&mask)==mask for a in front)
        assert feasible_only(chosen,0,limit,arrival)==want
        exact+=1
    return exact

def risk(tot,diag,ms):
    # all integer-weight laws of the restricted equal-marginal family
    # when tot is even; diag is one diagonal cell weight.
    mass=(diag,tot//2-diag,tot//2-diag,diag)
    values=[sum(x for i,x in enumerate(mass) if (1<<i)&m) for m in ms]
    return max(values)

def native_witness(mask,arrival,deadline):
    # Choose a policy by solving the independently checked conjunction on
    # the specified support, and execute it on *all four* actual states.
    # Fallback outside that support is NOOP, not a hidden truth read.
    prescribed=tuple(s for i,s in enumerate(worlds) if (1<<i)&mask)
    flags=[]
    for x0,y0,d0,mark in worlds:
        w=make(7,1,(x0,y0),D(d0),"dict-normalized",mark)
        B=prescribed
        for t in range(deadline):
            if not B or all(s[:2]==TARGET for s in B):
                a=A.NOOP
            else:
                for cand in ACTION:
                    C=defaultdict(set)
                    for s in B:
                        u=update(s,cand)
                        C[all_obs(t+1,u,arrival,"bound")].add(u)
                    if all(feasible_only(tuple(sorted(v)),t+1,deadline,arrival) for v in C.values()):
                        a=cand;break
                else:raise AssertionError("witness reconstruction")
            obs,_,_,_,_=native.step(w,(a,A.NOOP))
            obs_id=json.dumps(freeze(obs[0]),sort_keys=True),mark if t+1>=arrival else None
            g=w.agents[0]
            assert obs_id==all_obs(t+1,(g.x,g.y,g.dir.value,mark),arrival,"bound")
            B=tuple(sorted({v for s in B if all_obs(t+1,(v:=update(s,a)),arrival,"bound")==obs_id}))
        flags.append((w.agents[0].x,w.agents[0].y)==TARGET)
    got=sum(1<<i for i,v in enumerate(flags) if v)
    assert got==mask
    return got

def main():
    S=tuple(enumerate(worlds))
    assert len({perceive(s) for _,s in S})==1
    rows={n:possible(S,n) for n in range(9)}
    timed={n:possible(S,5,0,n) for n in range(1,7)}
    assert rows=={0:(0,),1:(0,),2:(3,12),3:(3,12),4:(3,12),5:(3,5,10,12),6:(3,5,10,12),7:(3,5,10,12),8:(15,)}
    assert timed[1]==(15,) and timed[2]==timed[3]==(3,5,6,9,10,12) and all(timed[i]==rows[5] for i in (4,5,6))
    support_checks=sum(compare(S,front,t,99) for t,front in rows.items())+sum(compare(S,front,5,t) for t,front in timed.items())
    law_checks=0
    for m in range(1,41):
        whole=2*m
        for t in range(m+1):
            truth=max(m,2*t,whole-2*t)
            assert risk(whole,t,timed[2])==risk(whole,t,timed[3])==truth
            assert risk(whole,t,timed[4])==risk(whole,t,rows[5])==m
            assert risk(whole,t,timed[1])==whole
            law_checks+=1
    live={str(m):native_witness(m,2,5) for m in (3,5,6,9,10,12)}
    print(json.dumps({"evolving_native_masks":live,"subset_predicate_checks":support_checks,"equal_marginal_law_checks":law_checks,"timed_deadline5":timed,"mask_frontier":rows,"cut_states":possible.cache_info().currsize,
                      "native_transitions":update.cache_info().currsize},sort_keys=True,separators=(",",":")))
if __name__=="__main__":main()
