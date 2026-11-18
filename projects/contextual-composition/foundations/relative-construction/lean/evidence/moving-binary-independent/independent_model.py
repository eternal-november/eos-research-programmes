from itertools import permutations,product
P=list(permutations(range(3)));T=list(product(range(3),repeat=3))
id=(0,1,2)
def mul(a,b):return tuple(b[i] for i in a)
def inv(a):return tuple(a.index(i) for i in id)
def m(a,b):return tuple(mul(x,y) for x,y in zip(a,b))
def i(a):return tuple(inv(x) for x in a)
def conj(g,f):return m(m(g,f),i(g))
s=(1,0,2);l=(s,(1,0,2));r=(s,(0,2,1)); cell=m(l,i(r))
assert cell[0]==id and cell[1]!=id
t=[0]*6
for b,f in product(P,T):
 a=(b,f);L=conj(l,a);R=conj(r,a)
 assert m(L,cell)==m(cell,R)
 t[0]+=1
 t[1]+=b!=id and len(set(f))<3
 t[2]+=L[0]!=b
 t[3]+=m(L,cell)!=m(cell,a)
 t[4]+=m(L,i(cell))!=m(i(cell),R)
 t[5]+=m(L,cell)!=m(cell,(R[0],id))
print(cell,t)
r2=(id,r[1]);cell2=m(l,i(r2));assert cell2[0]!=id
assert all(m(conj(l,a),cell2)==m(cell2,conj(r2,a)) for a in product(P,T))
# Same objects, same published identity family, strictly over the base, but a
# reachable pair of total endpoints disagrees with the published identity
# fibre functors on fibre arrows.
g=(id,(1,0,2));ident=(id,id)
assert m(g,i(g))==ident
assert all(conj(g,(b,f))[0]==b for b,f in product(P,T))
n=sum(conj(g,(id,f))!=(id,f) for f in T);assert n>0
print('Matched identity components and strict base, but',n,'of 27 vertical arrows disagree.')
