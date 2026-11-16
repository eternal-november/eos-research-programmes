from fractions import Fraction as F
from itertools import product
p={0:F(2,5),1:F(3,5)}
mu={0:{0:F(1,3),1:F(2,3)},1:{0:F(3,4),1:F(1,4)}}
nu={0:{0:F(1,5),1:F(4,5)},1:{0:F(2,3),1:F(1,3)}}
xi={0:{0:F(1,7),1:F(6,7)},1:{0:F(3,8),1:F(5,8)}}
def b(a,w,i):return (a+w+i)%2
def c(b,z,j):return (b+z+j)%2
left={};right={}
for a,w,z0,z1 in product(range(2),repeat=4):
    zs=(z0,z1)
    mid=p[a]*mu[a][w]
    for i in range(2):mid*=nu[b(a,w,i)][zs[i]]
    for vs in product(range(2),repeat=4):
        val=mid
        for i,j in product(range(2),repeat=2):val*=xi[c(b(a,w,i),zs[i],j)][vs[2*i+j]]
        left[(a,w,z0,z1,*vs)]=val
for a,w in product(range(2),repeat=2):
    for z0,v00,v01,z1,v10,v11 in product(range(2),repeat=6):
        zs=(z0,z1);vss=((v00,v01),(v10,v11))
        val=p[a]*mu[a][w]
        for i in range(2):
            subtree=nu[b(a,w,i)][zs[i]]
            for j in range(2):subtree*=xi[c(b(a,w,i),zs[i],j)][vss[i][j]]
            val*=subtree
        right[(a,w,z0,z1,v00,v01,v10,v11)]=val
assert left==right and sum(left.values())==1
# Shared-state closure: n=2 flip, then m=3 flip.
for s in range(2):
    mid=[1-s]*2
    final=[[1-x]*3 for x in mid]
    assert all(y==s for ys in final for y in ys)
    assert not all(x==s for x in mid)
# Independently hidden identities may choose incompatible states.
assert (0,1)[0] != (0,1)[1]
# Nullary root consumes no continuation witnesses or probability factors.
assert sum(p[a]*mu[a][w] for a,w in product(range(2),repeat=2))==1
# Binary all-coupling compositor has distinct diagonal and independent laws.
diag={(x,y):F(x==y,2) for x,y in product(range(2),repeat=2)}
indep={(x,y):F(1,4) for x,y in product(range(2),repeat=2)}
assert diag!=indep
for law in (diag,indep):
    for x in range(2):
        assert sum(law[x,y] for y in range(2))==F(1,2)
        assert sum(law[y,x] for y in range(2))==F(1,2)
# Nested equality restrictions on two state coordinates commute exactly.
raw=list(product(range(2),repeat=6)) # (s,t,s1,t1,s2,t2)
close_s=lambda z:z[0]==z[2]==z[4]
close_t=lambda z:z[1]==z[3]==z[5]
st=[z for z in raw if close_s(z) and close_t(z)]
ts=[z for z in raw if close_t(z) and close_s(z)]
combined=[z for z in raw if (z[0],z[1])==(z[2],z[3])==(z[4],z[5])]
assert st==ts==combined and len(st)==4
# Augmented-vector tensor-to-pullback: common scalar, first tail, second tail.
def native_coefficient_map(v):
    v00,v01,v10,v11=v
    return (v00,v10,v01)
basis=[tuple(int(i==j) for i in range(4)) for j in range(4)]
assert [native_coefficient_map(v) for v in basis]==[(1,0,0),(0,0,1),(0,1,0),(0,0,0)]
print('PASS: 256 exact witness weights / triple bracketings; binary coupling distinction; branching double-toggle closure; nested state equalities; nullary law; native coefficient kernel.')
