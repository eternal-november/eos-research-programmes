from itertools import permutations, product
P=list(permutations(range(3))); I=P[0]
mul=lambda a,b:tuple(b[x] for x in a) # left-to-right
inv=lambda a:tuple(a.index(i) for i in range(3))
# Functor N = identity, inverse M acts by conjugation, unit u: id=>M and counit v:M=>id.
# G = conjugate of F=id by q. q: F=>G, acts naturally.
tot=bare=fw=0
for u,q in product(P,P):
 M=lambda a:mul(mul(inv(u),a),u)
 G=lambda a:mul(mul(inv(q),a),q)
 assert all(mul(g,u)==mul(u,M(g)) for g in P)
 d=mul(u,q)
 assert all(mul(g,d)==mul(d,G(M(g))) for g in P)
 assert mul(d,G(inv(u)))==q
 assert [a for a in P if mul(a,G(inv(u)))==q]==[d]
 tot+=1;bare+=d!=q;fw+=mul(d,G(u))!=q
print(tot,bare,fw)
# Two-object base arrow acts via a transposition on 3 fibre labels; source and
# target are the same diagram. Natural transformations are pairs of arbitrary
# maps commute with the crossing (not necessarily invertible or equal).
maps=list(product(range(3),repeat=3)); t=(1,0,2)
ns=[(a,b) for a,b in product(maps,repeat=2) if mul(a,t)==mul(t,b)]
print('total',len(ns),'of',len(maps)**2,'noninvertible',sum(len(set(a))<3 for a,b in ns),'unequal',sum(a!=b for a,b in ns),'equal but obstructed',sum((a,a) not in ns for a in maps))
