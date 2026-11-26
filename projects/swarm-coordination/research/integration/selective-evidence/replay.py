"""Abstract bounded unreliable evidence; no network or deployment interface."""
from itertools import product, combinations_with_replacement

def words(n, alphabet=(0,1)):
    return list(product(alphabet, repeat=n))

def diff(a,b):
    return sum(x!=y for x,y in zip(a,b))

def radius(code, candidates):
    return min(max(diff(w,x) for w in code) for x in candidates)

def upper_triple(code):
    columns=list(zip(*code))
    center=[int(sum(c)>1) for c in columns]
    loads=[diff(center,w) for w in code]
    k=max(range(3),key=loads.__getitem__)
    r=(sum(sorted(loads)[-2:])+1)//2
    delta=max(0,loads[k]-r)
    for i in range(len(columns)):
        if delta and code[k][i]!=center[i]:
            center[i]=code[k][i]
            delta-=1
    assert delta==0 and max(diff(w,center) for w in code)==r
    return r

def legal(tape, code, sites):
    eligible=[set(a) for w,a in zip(code,sites) if diff(tape,w)<=1]
    return set.intersection(*eligible) if eligible else None

code=[(0,0,0),(1,1,0),(1,0,1)]
sites=[{"left","center"},{"center","right"},{"left","right"}]
assert all(a&b for a in sites for b in sites)
assert legal((1,0,0),code,sites)==set()
extended=[w+(int(i==0),) for i,w in enumerate(code)]
assert all(legal(y,extended,sites)!=set() for y in words(4))
stacked=[((w[0],w[0]),w[1],w[2]) for w in code]
assert legal(((1,1),0,0),stacked,sites)==set()
print("two-history checks pass; one report still admits a three-world obstruction")
print("new independent domain restores service; repeating a co-owned report does not")

checked=0
for n in range(1,6):
    w=words(n)
    for x in combinations_with_replacement(w,3):
        assert upper_triple(x)==radius(x,w)
        checked+=1
print("binary triple radius comparisons:",checked)
tet=[(0,0,0),(0,1,1),(1,0,1),(1,1,0)]
assert all(diff(a,b)<=2 for a in tet for b in tet) and radius(tet,words(3))==2
assert radius([(i,i) for i in range(3)],words(2,range(3)))==2
print("four binary histories or two ternary domains defeat the simple diameter formula")
