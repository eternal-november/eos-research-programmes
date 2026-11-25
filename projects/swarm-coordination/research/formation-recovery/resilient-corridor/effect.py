"""Two-epoch report custody with relay radio loss after fan-out."""
from itertools import combinations,product

def sets(n,k):
    for size in range(min(n,k)+1):
        for a in combinations(range(n),size):
            yield frozenset(a)

def physical_trial(stored,armed,silent):
    # Holds actual copies through the first transition. A second-epoch
    # delivery comes from a distinct assigned, still-powered slot.
    live=stored-silent
    return bool(live & armed)

def feasible(n,max_stores,slots,k,visible_at_forward):
    D=tuple(sets(n,k))
    for stored in sets(n,max_stores):
        if visible_at_forward:
            if slots and all(stored-silent for silent in D):return True
        else:
            for armed in sets(n,slots):
                if all(physical_trial(stored,armed,silent) for silent in D):return True
    return False

if __name__=="__main__":
    ncases=0
    for n,a,c,k in product(range(5),range(5),range(5),range(5)):
        assert feasible(n,a,c,k,False)==(min(n,a,c)>k)
        assert feasible(n,a,c,k,True)==(min(n,a)>k and c>0)
        ncases+=2
    print(ncases,"physical custody/vetted-slot comparisons")
    assert feasible(2,2,2,1,False)
    assert not feasible(2,1,2,1,False)
    assert not feasible(2,2,1,1,False)
    assert feasible(2,2,1,1,True)
    print("two-hop geometry survives one frozen deletion; timed delivery needs fan-out and slots or timely identification")
