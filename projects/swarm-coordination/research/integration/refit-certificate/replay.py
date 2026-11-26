"""Exact affine refit and comparison of full, retained, and stale releases."""
from fractions import Fraction as F
from itertools import combinations, product


def solve(a,b):
    rows = [[F(x) for x in row]+[F(y)] for row,y in zip(a,b)]
    n = len(a)
    for m in range(n):
        i = next(i for i in range(m,n) if rows[i][m])
        rows[m],rows[i] = rows[i],rows[m]
        p = rows[m][m]
        rows[m] = [v/p for v in rows[m]]
        for j in range(n):
            if j!=m:
                c=rows[j][m]
                rows[j]=[x-c*y for x,y in zip(rows[j],rows[m])]
    return tuple(r[-1] for r in rows)


def learn(data):
    x = [[1,a,b] for a,b,y in data]
    return solve([[sum(v[i]*v[j] for v in x) for j in range(3)] for i in range(3)],
                 [sum(v[i]*z[2] for v,z in zip(x,data)) for i in range(3)])


def hull(points):
    def side(p,q,r):
        return (q[0]-p[0])*(r[1]-p[1])-(q[1]-p[1])*(r[0]-p[0])
    def edge(seq):
        out=[]
        for p in seq:
            while len(out)>=2 and side(out[-2],out[-1],p)<=0:
                out.pop()
            out.append(p)
        return out
    pts=sorted(set(points))
    return pts if len(pts)<2 else edge(pts)[:-1]+edge(reversed(pts))[:-1]


def lower(points,model,error=0,age_debit=0):
    b,w1,w2=model
    return min(b+w1*p+w2*q for p,q in points)-error-age_debit


old = learn([(0,0,2),(1,0,3),(0,1,2),(1,1,3)])
new = learn([(0,0,0),(1,0,1),(0,1,1),(1,1,2)])
assert old == (2,1,0) and new == (0,1,1)
clouds = (((1,2),(2,1)),((1,1),(2,2)))
error=F(1,4)
threshold=F(5,2)
assert [lower(c,old,error) for c in clouds]==[F(11,4)]*2
assert [lower(c,new,error) for c in clouds]==[F(11,4),F(7,4)]
assert all(lower(c,old,error)>=threshold for c in clouds)
assert [lower(hull(c),new,error)>=threshold for c in clouds]==[True,False]
assert [lower(hull(c),new,error,F(1,4))>=threshold for c in clouds]==[True,False]
assert [lower(hull(c),new,error,F(1,3))>=threshold for c in clouds]==[False,False]
print("same raw marginals and old lower bound 2.75; refit gives 2.75 or 1.75")
print("fresh compatible raw capsule preserves A exactly through age debit 0.25")

# Compare perfectly received model update with one decision consumer that
# omits the current coefficient vector. Closure/authority are already valid
# inputs to both consumers. This is not a freshness/transport failure.
assert (lower(clouds[1], old, error)>=threshold
        and not lower(clouds[1],new,error)>=threshold)
print("known refit omitted from a legacy admission: old clear / current uncertified")

grid=list(product(range(3),repeat=2))
count=0
for n in range(1,len(grid)+1):
    for pts in combinations(grid,n):
        profile=hull(pts)
        for w1,w2 in product(range(-3,4),repeat=2):
            line=(0,w1,w2)
            assert lower(pts,line)==lower(profile,line)
            count+=1
print("matched affine hull comparisons:",count)

old_pair = ((-1,0),(1,0))
with_inner = old_pair + ((0,0),)
assert hull(old_pair)==hull(with_inner)
square=lambda p:sum(x*x for x in p)
assert min(map(square,old_pair))==1 and min(map(square,with_inner))==0
print("one nonlinear refit can distinguish clouds with identical hull")
