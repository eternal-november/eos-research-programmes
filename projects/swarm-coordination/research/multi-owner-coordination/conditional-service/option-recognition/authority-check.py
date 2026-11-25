"""Independent robust physical guard: consent and a fee do not grant use."""
from itertools import product

def local_decision(worlds,reads):
    # worlds carries verifier truth. The actor receives only the evidence row.
    # A joint start requires permission, actual no overlap, and local admissible
    # evidence. Otherwise make no shared start and leave someone else's work in place.
    cells={}
    for w,read in zip(worlds,reads):
        cells.setdefault(read,[]).append(w)
    return {read:all(permission and free for permission,free in rows)
            for read,rows in cells.items()}

def main():
    n=0
    atoms=list(product((False,True),repeat=2))
    for worlds in product(atoms,repeat=3):
        for reads in product(range(2), repeat=3):
            rule=local_decision(worlds,reads)
            feasible=[]
            for candidate in product((False,True),repeat=2):
                if all(not candidate[read] or (p and c) for (p,c),read in zip(worlds,reads)):
                    feasible.append(candidate)
            assert all(not c[r] or rule[r] for c in feasible for r in rule)
            assert all(not rule[r] or (p and c) for (p,c),r in zip(worlds,reads))
            n+=1
    assert local_decision(((True,True),(True,False)),(0,0))=={0:False}
    assert local_decision(((True,True),(True,False)),(0,1))=={0:True,1:False}
    print(n,'source permutations checked; identical receipt requires refusal even with both owners consenting')

if __name__=='__main__':main()
