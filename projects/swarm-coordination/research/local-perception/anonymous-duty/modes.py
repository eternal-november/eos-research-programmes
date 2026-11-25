"""Choosing primitive observation positions with uncertain source cut."""
from itertools import combinations
from probe import worst_compatible

def masks(n):
    for k in range(n+1):
        yield from combinations(range(n),k)

def valid_modes(scopes, reads, targets, know_cut):
    if know_cut:
        return all(worst_compatible(s,reads,targets)==1 for s in scopes)
    return worst_compatible(set().union(*scopes),reads,targets)==1

def distinguishing(scopes, read, targets, know_cut):
    sensor=sum(1<<j for j in read)
    target=sum(1<<j for j in targets)
    family=scopes if know_cut else (set().union(*scopes),)
    return all(((x^y)&sensor)!=0 for W in family
               for x,y in combinations(W,2) if (x^y)&target)

def optimum(scopes,n,targets,know_cut):
    return next((len(r) for r in masks(n) if valid_modes(scopes,r,targets,know_cut)),None)

def main():
    count=0
    for n in range(2,8):
        W=[{0,g} for g in range(1,1<<n,2)]
        for r in masks(n):
            for t in masks(n):
                for known in (True,False):
                    assert distinguishing(W,r,t,known)==valid_modes(W,r,t,known)
                    count+=1
        assert optimum(W,n,range(n),True)==1
        assert optimum(W,n,range(n),False)==n
        assert optimum(W,n-1,[n-1],True)==1
        assert optimum(W,n-1,[n-1],False) is None
    print(count,'matched scopes/observations/targets comparisons')
    print('one fixed read works for every reported source cut')
    print('n fixed reads are needed to recover all duties if the cut is not reported')
    print('if the target cell is out of reach, an unreported cut can make its duty undecidable')
if __name__=='__main__':main()
