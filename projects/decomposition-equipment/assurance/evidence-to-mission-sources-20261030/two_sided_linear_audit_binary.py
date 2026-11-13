from itertools import product

def parity(v): return v.bit_count()&1

def subs(n):
 s={frozenset([0])}
 for v in range(1,1<<n):
  s.update(frozenset(set(t)|{x^v for x in t}) for t in list(s))
 return s

def check(a,u):
 n=a+u; V=range(1<<n); A=set(range(1<<a)); U=range(1<<u); mask=(1<<a)-1
 count=0
 for S in subs(n):
  rows=[r for r in V if all(not parity(r&s) for s in S)]
  W=[s for s in S if not(s&mask)]
  for columns in product(U,repeat=n):
   L=[0]*(1<<n)
   for v in V:
    for i in range(n):
     if (v>>i)&1: L[v]^=columns[i]
   obs={s&mask for s in S if L[s]==0}==A
   base={v&mask for v in V if L[v]==0}==A
   for B in U:
    imB={0,B}; T=[v for v in V if L[v] in imB]
    feas=obs or (imB<={L[w] for w in W} and base)
    for C in (0,1):
     for m in V:
      M=[parity(m&v) for v in V]
      if set(T)<=S:
       out=all(M[v]==0 for v in V if L[v]==0)
      else:
       out=any(parity(d&B)==C and all(parity(d&L[v])==M[v] for v in V) for d in U)
      actual=True
      for r in rows:
       fixed=[v for v in V if L[v]^(B if parity(r&v) else 0)==0]
       if {v&mask for v in fixed}!=A or any(M[v]^(C if parity(r&v) else 0) for v in fixed):
        actual=False; break
      if actual!=(feas and out):
       raise Exception((a,u,S,columns,B,C,m,feas,out,actual))
      count+=1
 print(a,u,count,'PASS',flush=True)
check(1,1)
check(1,2)
check(2,1)
