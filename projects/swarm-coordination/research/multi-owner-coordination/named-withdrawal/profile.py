"""Exhaustive finite comparison for reusable named-withdrawal query profiles."""
from collections import Counter,defaultdict
from itertools import permutations
from math import factorial,prod,comb
from random import Random
import json
from release import role_signatures,placement_profile

def compare(n,rights,new):
    degrees=role_signatures(n,rights)
    enlarged=role_signatures(n,(*rights,new))
    old_classes=Counter(degrees)
    quotient=0
    groups=defaultdict(set)
    concrete={}
    seen=0
    for p in permutations(range(n)):
        profile=placement_profile(p,degrees)
        ext=placement_profile(p,enlarged)
        # Independently produce query rows by actual mechanism: remove all
        # authorized named shelves, ask which bay is empty for each query.
        old_row=tuple(tuple(j for j,cargo in enumerate(p) if cargo in allowed)
                      for allowed in rights)
        new_row=tuple(j for j,cargo in enumerate(p) if cargo in new)
        if old_row not in concrete:concrete[old_row]=profile
        assert concrete[old_row]==profile
        groups[profile].add((new_row,ext))
        seen+=1
    assert len(groups)==len(concrete)==factorial(n)//prod(factorial(c) for c in old_classes.values())
    authorized=Counter(degrees[x] for x in new)
    extensions=prod(comb(sz,authorized[d]) for d,sz in old_classes.items())
    for images in groups.values():
        raw={r for r,_ in images};q={x for _,x in images}
        assert len(raw)==len(q)==len(images)==extensions
    return (seen,len(groups),extensions)


def campaign():
    rng=Random(20261126)
    matched=[[2,[],[0]],[4,[{0,1},{2,3}],[0,2]],
             [6,[{0,1,2},{3,4,5}],[0,2,4]]]
    profiles=0; exact_invocations=0; boundary=[]
    for n,rights,new in matched:
        r=compare(n,rights,new)
        boundary.append((n,*r))
        profiles+=1;exact_invocations+=r[0]
    for n in range(1,8):
        for i in range(9):
            q=tuple(frozenset(j for j in range(n) if rng.randrange(2))
                    for _ in range(i%5))
            field={j for j in range(n) if rng.randrange(2)}
            x,_,_=compare(n,q,field)
            exact_invocations+=x;profiles+=1
    print(json.dumps(dict(families=profiles,placement_checks=exact_invocations,
                          calibration=boundary),sort_keys=True,indent=2))

if __name__=='__main__':campaign()
