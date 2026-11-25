"""Append-only base, same generation, no reentry, and a sustainable physical guarantee."""
from itertools import product
from receiver import Kind, Key, Fact, Job, choose
keys={k:Key(k,"named bay","old generation","new operation") for k in Kind}
job=Job(frozenset(keys.values()),0,7,2)

def decide(bound,k,closed,clear,receipt,cut,grant):
    facts=[]
    # Successful publication may still be in flight. Include any unresolved
    # crash window in the upper bound. 'closed' includes all enqueue and retry.
    if closed and bound < k:
        facts.append(Fact(keys[Kind.FENCED],receipt,0,8))
    if clear:
        facts.append(Fact(keys[Kind.QUIESCENT],0,0,8))
    if grant:
        facts.append(Fact(keys[Kind.GRANTED],0,0,8))
    return choose(job,cut,facts)

def direct(a,p,k,closed,clear,receipt,cut,grant):
    largest=len(range(a,p+1))
    options=({r for r in range(a,p+1)} if closed and receipt<=cut
             else {r for r in range(a,max(k,p)+1)})
    assert len(options)>=largest
    for s in range(cut,7):
        if all(clear and grant and t<7 and all(r<k for r in options)
               for t in range(s,s+2)):
            return s
    return None

total=false_reflected=0
for a,p,k,closed,clear,receipt,cut,grant in product(
    range(6),range(6),range(1,7),(False,True),(False,True),(0,2),range(8),(False,True)):
    if a>p: continue
    exact=decide(p,k,closed,clear,receipt,cut,grant)
    assert exact==direct(a,p,k,closed,clear,receipt,cut,grant)
    if exact is None and decide(a,k,closed,clear,receipt,cut,grant) is not None:
        false_reflected+=1
    total+=1
# Old acknowledgement and local attempted marker are equal. Only emitted
# released extensions are plausible at the receiver under a complete log.
assert decide(0,1,True,True,1,1,True)==1
assert decide(1,1,True,True,1,1,True) is None
# A possible emission in a crash gap has to be accounted for like a real one.
assert decide(1,1,True,True,1,1,True) is None
# Snapshot empty alone cannot admit: the scopes differ on whether entry can recur.
assert decide(0,1,False,True,1,1,True) is None
assert decide(0,1,True,False,1,1,True) is None
print(f"matched direct support and deadline: {total} cases")
print(f"false admits if reflected prefix substitutes for publication bound: {false_reflected}")
print("identical attempted/reflected state: logged no-emission admits; possible emission refuses")
print("stale/missing fence or missing sustained clearance: refuses")
