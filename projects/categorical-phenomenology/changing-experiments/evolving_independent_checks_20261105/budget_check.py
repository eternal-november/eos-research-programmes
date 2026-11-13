from itertools import product
from collections import deque
v=lambda n:list(product(range(3),repeat=n))
le=lambda a,b:all(x<=y for x,y in zip(a,b))
add=lambda a,b:tuple(x+y for x,y in zip(a,b))
def vals(n,maxi):return list(product(range(maxi+1),repeat=n))
def Cv(C,a):return tuple(sum(c*x for c,x in zip(row,a)) for row in C)
def alloc(n,a):return [(p,q) for p in vals(n,max(a,default=0)) for q in vals(n,max(a,default=0)) if le(add(p,q),a)]
def ck(C,a):
 m=len(a);d=len(C);ca=Cv(C,a); X=alloc(m,a);Y=alloc(d,ca)
 D=lambda v:(Cv(C,v[0]),Cv(C,v[1]));boolok=setok=catok=True
 for p,q in Y:
  K=[x for x in X if le(p,D(x)[0]) and le(q,D(x)[1])]
  boolok &= bool(K)
  if K:
   seen={K[0]}; todo=[K[0]]
   while todo:
    x=todo.pop()
    for y in K:
     if y not in seen and ((le(x[0],y[0]) and le(x[1],y[1])) or (le(y[0],x[0]) and le(y[1],x[1]))):seen.add(y);todo.append(y)
   setok &= len(seen)==len(K)
  else:setok=False
 # D equivalence for finite posets iff bijection onto all Y and order reflection (preimages equal cannot be iso unless equal)
 image=[D(x) for x in X];catok=len(set(image))==len(image)==len(Y) and set(image)==set(Y)
 if catok:
  for x in X:
   for y in X:
    catok &= (le(x[0],y[0]) and le(x[1],y[1])) == (le(D(x)[0],D(y)[0]) and le(D(x)[1],D(y)[1]))
 return boolok,setok,catok
# bounded matrices and inputs
results=[]
for entries in product(range(3),repeat=4):
 C=(entries[:2],entries[2:]); status=[True]*3
 for a in product(range(2),repeat=2):
  out=ck(C,a);status=[x and y for x,y in zip(status,out)]
 columns=list(zip(*C)); boolpred=all(sum(v)!=0 and sum(v)!=1 and False or sum(v)<=1 for v in columns); setpred=boolpred and all(sum(x>0 for x in row)<=1 for row in C); catpred=setpred and all(sum(v)>0 for v in columns)
 if tuple(status)!=(boolpred,setpred,catpred):results.append((C,status,(boolpred,setpred,catpred)))
print('checked',81,'mismatches',len(results));print(results[:5])
