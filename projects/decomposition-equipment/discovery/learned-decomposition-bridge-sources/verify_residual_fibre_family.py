"""Exact finite structural checks for the growing continuous example.
Does not numerically prove identifiability or simulate a noisy decoder.
"""
from fractions import Fraction as F
import json

def determinant(a):
    a=[[F(x) for x in r] for r in a]
    n=len(a); det=F(1)
    for j in range(n):
        i=next((i for i in range(j,n) if a[i][j]),None)
        if i is None:return F(0)
        if i!=j:a[j],a[i]=a[i],a[j];det=-det
        p=a[j][j];det*=p
        for k in range(j,n):a[j][k]/=p
        for i in range(j+1,n):
            p=a[i][j]
            for k in range(j,n):a[i][k]-=p*a[j][k]
    return det

results=[]
for n in range(3,9):
    rows=[{j for j in range(n) if abs(i-j)<=1} for i in range(n)]
    cols=rows
    c=[[rows[i]<=rows[j] and cols[i]<=cols[j] for j in range(n)] for i in range(n)]
    assert all(not(c[i][j] and c[j][i]) for i in range(n) for j in range(n) if i!=j)
    strict=[(i,j) for i in range(n) for j in range(n) if i!=j and c[i][j]]
    assert strict
    edges=[(i,j) for i in range(n) for j in sorted(rows[i])]
    m=len(edges);assert m==3*n-2
    v=[[a**k for k in range(1,m+1)] for a in range(1,m+1)]
    d=determinant(v)
    expected=1
    for a in range(1,m+1):expected*=a
    for a in range(1,m+1):
        for b in range(a+1,m+1):expected*=b-a
    assert d==expected and d>0
    cycle=lambda i,j:i==j or ((i-j)%n in (1,n-1))
    assert all(cycle(i,j) for i,j in edges)
    assert all(cycle(i,(i+1)%n) for i in range(n))
    results.append({"n":n,"edges":m,"strict_preorder_pairs":strict,
                    "all_sccs_singletons":True,"full_hessian_span_vandermonde":True,
                    "fits_cycle_raw_ports":True})
print(json.dumps({"all_checks_passed":True,"checked_family_members":results},indent=2))
