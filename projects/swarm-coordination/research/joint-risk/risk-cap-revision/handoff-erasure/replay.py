from fractions import Fraction as Q
from itertools import combinations, product
from functools import lru_cache

@lru_cache(maxsize=None)
def couplings(r,e):
    # E=erasure; coordinates o=mass(O and E), f=mass(F and E).
    # Remaining erased mass belongs to neither outcome.
    H=[(-1,0,0),(0,-1,0),(1,0,r),(0,1,r),(1,1,e),(-1,-1,1-2*r-e)]
    return vertices(H)

def vertices(H):
    ans=set()
    for (a,b,c),(d,e,f) in combinations(H,2):
        det=a*e-b*d
        if not det: continue
        x=Q(c*e-b*f,det)
        y=Q(a*f-c*d,det)
        if all(u*x+v*y<=w for u,v,w in H): ans.add((x,y))
    return tuple(sorted(ans))

def metrics(r,e,o,f,q,m):
    # q: admit on erased record; m: pick disjoint-failure route on delivered record.
    q,m=Q(q),Q(m)
    cap=r+q*f/2+m*(r-f)
    work=1-e-r+q*e+(1-m-q/2)*o+(m-q/2)*f
    return cap,work

def solve(r,e,c):
    C=couplings(r,e)
    # Add all pairwise utility ties: the lower envelope is linear on each cell.
    H=[(-1,0,0),(0,-1,0),(1,0,1),(0,1,1)]
    H.extend((f/2,r-f,c-r) for o,f in C)
    L=[(1-e-r+o,e-(o+f)/2,f-o) for o,f in C]
    parts=[]
    for (k,a,b),(l,d,j) in combinations(L,2):
        if a!=d or b!=j: parts.extend([(a-d,b-j,l-k)])
    # Intersections with utility-tie lines need not satisfy those equalities
    # as inequalities. Compute all line intersections, clip only base constraints.
    candidates=set()
    for (a,b,k),(d,j,l) in combinations(H+parts,2):
        det=a*j-b*d
        if det:
            q,m=Q(k*j-b*l,det),Q(a*l-k*d,det)
            if all(u*q+v*m<=w for u,v,w in H): candidates.add((q,m))
    return max((min(metrics(r,e,o,f,q,m)[1] for o,f in C),q,m)
               for q,m in candidates)

def direct(r,e,o,f,policy):
    # Two fair private bits, disjoint old/additional loss, fixed same-episode
    # erasure correlation. Evaluate actual outcomes, not the regret formula.
    risk=work=admitted=0
    for u,v,k,E in product(range(2),range(2),range(3),range(2)):
        p=((o,f,e-o-f) if E else (r-o,r-f,1-2*r-e+o+f))[k]/4
        a=policy[(2 if E else u)*2+v]
        miss_old=k==0
        miss_new=a!=0 and k==(0 if a==1+(u^v) else 1)
        risk+=p*(miss_old or miss_new)
        work+=p*(a!=0 and not miss_new)
        admitted+=p*(a!=0)
    return risk,work,admitted

def tests():
    cases=0
    choices=tuple(product(range(3),repeat=6))
    for r,e in product((Q(1,8),Q(1,4),Q(1,3)),(Q(0),Q(1,8),Q(1,4),Q(1,2),Q(3,4),Q(1))):
        if e==1: continue
        for o,f in couplings(r,e):
            for pol in choices:
                if not all(pol[i] for i in range(4)):continue
                q=Q(sum(bool(a) for a in pol[4:]),2)
                m=Q(sum(pol[2*u+v]!=1+(u^v) for u,v in product(range(2),repeat=2)),4)
                assert direct(r,e,o,f,pol)[:2]==metrics(r,e,o,f,q,m)
                cases+=1
    # At e=1/4, a record with that same aggregate erasure rate can be much
    # less useful if erasure clusters in the latent branch that adds loss.
    family=0
    for r in (Q(1,8),Q(1,4),Q(1,3)):
        for k in range(17):
            d=k*r/16
            opt=solve(r,r,r+d)
            assert opt[0]==min(1-r,1-2*r+2*d)
            family+=1
    print("Closed form vs all LP cells:",family)
    r,e,c=Q(1,4),Q(1,4),Q(5,16)
    robust=solve(r,e,c)
    assert robust==(Q(5,8),Q(1,2),Q(1,4))
    independent=metrics(r,e,r*e,r*e,1,0)
    assert independent==(Q(9,32),Q(3,4))
    worked=(Q(0),Q(1,4))
    assert metrics(r,e,*worked,1,0)==(Q(3,8),Q(5,8))
    print("Enumerated policy/coupling corners:",cases)
    print("At 1/4 erasure, robust (work, erased admission, delivered misrouting):",*robust)
    print("Full admission with independent erasure (risk, work):",*independent)
    print("Full admission with the same marginal erasure clustered on the extra loss:",*metrics(r,e,*worked,1,0))

if __name__=="__main__":
    tests()
