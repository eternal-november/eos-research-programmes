"""Exact finite regression checks for the independent assumption review."""
from fractions import Fraction as F
from itertools import combinations, product
import json


def marginal(p, S):
    q = {}
    for x, v in p.items():
        y = tuple(x[i] for i in S)
        q[y] = q.get(y, F(0)) + v
    return q


def tv(p, q):
    return sum(abs(p.get(x, F(0)) - q.get(x, F(0))) for x in p.keys() | q.keys()) / 2


def product_law(p, partition):
    rows = [marginal(p, B) for B in partition]
    n = len(next(iter(p)))
    q = {}
    for cells in product(*(tuple(r) for r in rows)):
        x = [None] * n
        weight = F(1)
        for B, row, cell in zip(partition, rows, cells):
            weight *= row[cell]
            for i, v in zip(B, cell):
                x[i] = v
        q[tuple(x)] = weight
    return q


# A memoryless high-order dependence is invisible to every proper cylinder.
m = 5
p = {}; q = {}
for x in product((0,1), repeat=m):
    b = sum(x) % 2
    p[x+(b,)] = F(1,2**m)
    q[x+(1-b,)] = F(1,2**m)
for k in range(m+1):
    for S in combinations(range(m+1), k):
        assert marginal(p,S) == marginal(q,S)
assert tv(p,q) == 1

# Pairwise-independent but irreducible full-support triple, theta=1/2.
theta = F(1,2)
p3 = {x:F(1,8)*(1+theta*(-1)**sum(x)) for x in product((0,1),repeat=3)}
assert all(v>0 for v in p3.values())
for S in combinations(range(3),2):
    assert all(v==F(1,4) for v in marginal(p3,S).values())
for i in range(3):
    split=((i,),tuple(j for j in range(3) if j!=i))
    assert tv(p3,product_law(p3,split)) == theta/2

# Irreducible-subset hypergraph recovers this triple and an independent pair.
p5 = {}
for x in product((0,1), repeat=5):
    p5[x] = p3[x[:3]] * F(1,4) * (1+F(1,3)*(-1)**sum(x[3:]))
parent = list(range(5)); edges=[]
def find(i):
    while parent[i]!=i:
        i=parent[i]
    return i
for size in (2,3):
    for S in combinations(range(5),size):
        sub = marginal(p5,S)
        independent_split=False
        for k in range(1,size):
            for A in combinations(range(size),k):
                B=tuple(i for i in range(size) if i not in A)
                if sub == product_law(sub,(A,B)):
                    independent_split=True
        if not independent_split:
            assert set(S)<=set((0,1,2)) or set(S)<=set((3,4))
            edges.append(S)
            root=find(S[0])
            for i in S[1:]: parent[find(i)] = root
components={}
for i in range(5): components.setdefault(find(i),[]).append(i)
assert sorted(components.values()) == [[0,1,2],[3,4]]

# Immediate output equality is not stable recursive equivalence.
output=lambda state:state[0]
step=lambda state:(state[1],state[0])
s,t=(0,0),(0,1)
assert output(s)==output(t)
assert output(step(s))!=output(step(t))

# Episode-start controller mixtures do not cover within-episode switching.
response0=lambda actions:0
response1=lambda actions:int(actions[0]!=actions[1])
assert all(response0(a)==response1(a) for a in ((0,0),(1,1)))
assert response0((0,1))!=response1((0,1))

# Fixed persistent source versus fresh independent source differs temporally.
persistent={(0,0):F(1,2),(1,1):F(1,2)}
fresh={x:F(1,4) for x in product((0,1),repeat=2)}
assert all(marginal(persistent,(i,))==marginal(fresh,(i,)) for i in range(2))
assert tv(persistent,fresh)==F(1,2)

# Integer response spacing: a nonzero offset cannot preserve +/-1 noise surely.
for offset in range(-10,11):
    violation=F(sum(abs(offset+e)!=1 for e in (-1,1)),2)
    assert offset==0 or violation>=F(1,2)

print(json.dumps({'status':'PASS','parity_parent_bits':m,
    'proper_marginals_identical':True,'full_parity_TV':'1',
    'pairwise_invisible_triple_split_TV':str(theta/2),
    'innovation_groups':sorted(components.values()),'irreducible_hyperedges':edges,
    'one_step_merge_not_recursive':True,'uncovered_controller_switch_detected':True,
    'persistent_vs_fresh_TV':str(tv(persistent,fresh))},indent=2))
