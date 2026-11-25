"""Source-role identity and validated reuse of generation tags."""
from collections import Counter
from random import Random

def safe(principals,tags,age):
    return all(principals[j]!=principals[i] or tags[i]!=tags[j]
               for i in range(len(tags)) for j in range(max(0,i-age),i))
def multiplicity(principals,age):
    return max((max(Counter(principals[max(0,i-age):i+1]).values())
                for i in range(len(principals))),default=0)
def assign(principals,age):
    tags=[]
    for i,p in enumerate(principals):
        recent={tags[j] for j in range(max(0,i-age),i) if principals[j]==p}
        c=next(t for t in range(age+1) if t not in recent)
        tags.append(c)
    return tuple(tags)
def colour(g,age):return g//2%(age//2+1)

def main():
    rng=Random(225199)
    z=0
    for _ in range(660):
        age=rng.randrange(0,12)
        owners=tuple(rng.randrange(3) for i in range(rng.randrange(1,60)))
        C=assign(owners,age)
        assert safe(owners,C,age) and max(C)+1==multiplicity(owners,age)
        z+=1
    print(z,'window-clique and greedy reuse comparisons with authentic principal identity')
    for L in range(12):
        owners=tuple(i%2 for i in range(400))
        good=tuple(colour(i,L) for i in range(400))
        assert safe(owners,good,L)
        assert multiplicity(owners,L)==L//2+1
        assert not safe(owners,good,2*(L//2+1))
    for L in (2,3,6,7):
        M=L//2+1
        assert not safe(tuple(i%2 for i in range(20)),tuple(i%M for i in range(20)),L)
    print('alternating actual signer needs floor(L/2)+1 tag values; the simpler modulo-M generation rule can fail')
if __name__=='__main__':main()
