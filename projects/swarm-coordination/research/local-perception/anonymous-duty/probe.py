"""A preliminary exact observation probe, not an independent fixture.

Each cell has two otherwise anonymous carts. An orientation bit locates
the named cart with an old duty. A recorded physical coupled movement
flips a set of cells jointly; a local move flips just that cell. The
choices are unknown and need not be independent of time. The family
below admits all combinations of the actual event generators.
"""
from itertools import combinations
from random import Random

def closure(gens):
    states={0}
    for g in gens:
        states |= {x^g for x in states}
    return states

def rank(xs):
    piv={}
    for x in xs:
        while x:
            b=x.bit_length()-1
            if b not in piv:
                piv[b]=x
                break
            x^=piv[b]
    return len(piv)

def project(x,positions):
    return sum(((x>>p)&1)<<i for i,p in enumerate(positions))

def worst_compatible(states, seen, targets):
    fibres={}
    for s in states:
        fibres.setdefault(project(s,seen),set()).add(project(s,targets))
    return max(map(len,fibres.values()))

def main():
    # Same post-cut visual occupancy, same architecture, same one-way check.
    # A coupled move occurred during occlusion; the later break did not
    # move a cart. A break before the move permits two independent flips.
    cases=(((0b11,),0,1), ((0b01,0b10),0,1))
    for gens,look,want in cases:
        print('decision classes after one signed read:',
              worst_compatible(closure(gens),[look],[want]))
    rng=Random(1837); total=0
    for n in range(1,9):
        for _ in range(75):
            gs=[rng.randrange(1<<n) for _ in range(rng.randrange(1,n+2))]
            states=closure(gs)
            for m in range(1<<n):
                read=[i for i in range(n) if (m>>i)&1]
                # Query all named duties, or only alternating sites.
                for target in (list(range(n)),list(range(0,n,2))):
                    joined=read+target
                    residual=rank(project(g,joined) for g in gs)-rank(project(g,read) for g in gs)
                    assert worst_compatible(states,read,target)==1<<residual
                    total+=1
    print(total,'exact source-enumeration versus residual-rank comparisons')
if __name__=='__main__':main()
