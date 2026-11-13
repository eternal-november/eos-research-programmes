#!/usr/bin/env python3
"""Independent finite regression of the explicitly proved cyclic formulas; no proof by sampling."""
import json, math
from pathlib import Path

def lam(n,r,b,a): return ((a if b==0 else r*a)%n,b)
def check_diagrams(n,r):
    units=all(lam(n,r,0,a)==(a,0) for a in range(n)) and all(lam(n,r,b,0)==(0,b) for b in range(2))
    baa=True; bba=True
    for b in range(2):
        for a in range(n):
            for ap in range(n):
                c,d=lam(n,r,b,a); cp,dp=lam(n,r,d,ap)
                baa &= lam(n,r,b,(a+ap)%n)==((c+cp)%n,dp)
            for bp in range(2):
                c,d=lam(n,r,bp,a); cp,dp=lam(n,r,b,c)
                bba &= lam(n,r,(b+bp)%2,a)==(cp,(dp+d)%2)
    return units,baa,bba

def mul(d,r,x,y): return ((x[0]+(r if x[1] else 1)*y[0])%d,(x[1]+y[1])%2)

checks=0; assoc=0; failures=0
for n in range(1,41):
    for r in range(-2,n+2):
        checks+=1
        u,aa,bb=check_diagrams(n,r)
        assert u and aa
        assert bb == ((r*r-1)%n==0)
        d=math.gcd(n,r*r-1)
        assert (r*r-1)%d==0 and math.gcd(r,d)==1
        a=(1%d,0); s=(0,1); one=(0,0)
        assert mul(d,r,s,s)==one
        assert mul(d,r,s,a)==mul(d,r,(r%d,0),s)
        assert len({(i%d,0) for i in range(n)})==d
        assert len({one,s})==2
        if not bb:
            failures+=1
            assert (1%n,0)!=((r*r)%n,0)
        if n<=12:
            elts=[(i,e) for i in range(d) for e in range(2)]
            for x in elts:
                for y in elts:
                    for z in elts:
                        assert mul(d,r,mul(d,r,x,y),z)==mul(d,r,x,mul(d,r,y,z))
                        assoc+=1
for k in range(1,9):
    n=5**k
    assert math.gcd(n,2*2-1)==1
    assert math.gcd(n,(-1)**2-1)==n
out={"status":"PASS","range":"1<=n<=40; -2<=r<=n+1","coefficient_cases":checks,"failed_BBA_cases":failures,"explicit_model_associativity_triples":assoc,"unbounded_family_regression_k":list(range(1,9)),"scope":"Finite regression only; universal claims proved in twisted_normal_forms.md."}
Path(__file__).with_name('verify_twisted_normal_forms.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
