from itertools import permutations,product
import json

def exact_interval(left,right,c):
    # First c pairs have an authoritative single-episode identity.
    # Remaining rows have no cross-episode constraints.
    old=sum(x or y for x,y in zip(left[:c],right[:c]))
    a,b=sum(left[c:]),sum(right[c:])
    return old+max(a,b),old+min(len(left)-c,a+b)

def main():
    checks=0
    for n in range(1,6):
        patterns=list(product((0,1),repeat=n))
        for a,b in product(patterns,repeat=2):
            for c in range(n+1):
                hit=set()
                for v in permutations(b[c:]):
                    q=b[:c]+v
                    hit.add(sum(x or y for x,y in zip(a,q)))
                lo,hi=exact_interval(a,b,c)
                assert hit==set(range(lo,hi+1))
                checks+=1
    print(json.dumps({"exact_interval_checks":checks,"full_permutations_through":5,
                      "unlinked_fixture":["1/2","1"],"linked_fixture":["1/2","1/2"]},
                     indent=2,sort_keys=True))
if __name__=="__main__":main()
