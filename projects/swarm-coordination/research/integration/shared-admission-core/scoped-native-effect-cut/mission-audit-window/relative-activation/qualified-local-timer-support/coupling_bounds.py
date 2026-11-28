"""Exact finite witness constructors, not inference of field likelihood."""
from itertools import combinations_with_replacement, product

def early_count(mask):
    return mask.bit_count()

def margins(words,n):
    return tuple(sum((w>>j)&1 for w in words) for j in range(n))

def successes(words,n):
    return sum(v in (0,(1<<n)-1) for v in words)

def nested(p,q):
    return [sum(1<<i for i,a in enumerate(p) if k<a) for k in range(q)]

def spread(p,q):
    acc=[0]
    for x in p:acc.append(acc[-1]+x)
    return [sum(1<<i for i in range(len(p)) if any(2*acc[i]<=2*k+1+2*q*j<2*acc[i+1]
                   for j in range(len(p)))) for k in range(q)]

comparisons=0; marginal_rows=0
for n in range(2,5):
    for q in range(2,6):
        bounds={}
        for words in combinations_with_replacement(range(1<<n),q):
            p=margins(words,n); wins=successes(words,n)
            lo,hi=bounds.get(p,(q,0))
            bounds[p]=(min(lo,wins),max(hi,wins))
            comparisons+=1
        for p in product(range(q+1),repeat=n):
            total=sum(p)
            lo=max(0,q-total)+max(0,total-(n-1)*q)
            hi=q-(max(p)-min(p))
            a,b=spread(p,q),nested(p,q)
            assert margins(a,n)==margins(b,n)==p
            assert (successes(a,n),successes(b,n))==(lo,hi)==bounds[p]
            assert all(early_count(k) in (total//q,(total+q-1)//q) for k in a)
            marginal_rows+=1
print(f"finite coupling laws {comparisons} marginal vectors {marginal_rows}")
