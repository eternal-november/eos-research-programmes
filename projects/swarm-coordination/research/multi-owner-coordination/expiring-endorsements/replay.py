"""Exact replay of expiring-endorsement ledger summaries."""
from functools import lru_cache
from itertools import combinations_with_replacement, product
from pathlib import Path
import json
import random
import sys

def sub(a,b): return a&b==a
def downward(a):
    return sum(1<<b for b in range(a+1) if sub(b,a))
def parts(a):
    return [b for b in range(a+1) if sub(b,a)]
def maximal(j):
    cs=[i for i in range(j.bit_length()) if j>>i&1]
    return [a for a in cs if not any(a!=b and sub(a,b) for b in cs)]
def width(j):
    return sum(bool(a) for a in maximal(j))
def ideal_word(word):
    j=1
    for b in word:j|=downward(b)
    return j
def lattice(m):
    n=1<<m
    return [j for j in range(1,(1<<n)-1,2) if all(
        not (j>>a&1) or sub(downward(a),j) for a in range(n))]
def read(ledger,j):
    return sum(sub(j,d) for d in ledger)
def direct(ledger,word):
    left=list(ledger)
    for c in word:
        left=[d for d in left if d>>c&1]
    return len(left)

def witness(j):
    pos=[];neg=[]
    m=maximal(j)
    assert m and all(m)
    for s in range(1<<len(m)):
        d=j
        for i,a in enumerate(m):
            if s>>i&1:d^=1<<a
        (neg if s.bit_count()%2 else pos).append(d)
    return pos,neg

def decoder(mass,measure):
    @lru_cache(None)
    def query(j):
        if j in measure:return measure[j]
        mx=maximal(j); t=len(mx)
        if 2**(t-1)<=mass: raise ValueError('permits unequal answers')
        top=(1<<t)-1
        z={s:query(ideal_word(a for i,a in enumerate(mx) if s>>i&1)) for s in range(top)}
        L,U=0,mass
        for b in range(top+1):
            coeff=(-1)**((top^b).bit_count())
            c=sum((-1)**((s^b).bit_count())*z[s] for s in range(top) if sub(b,s))
            if coeff==1:L=max(L,-c)
            else:U=min(U,c)
        assert L==U
        return L
    return query

def verify():
    rng=random.Random(18381)
    enumerations=[]; word_checks=witness_checks=codec_checks=bound_checks=step_checks=0
    for m in range(1,5):
        ds=lattice(m)
        ws={d:width(d) for d in ds}
        counts=[sum(k==w for k in ws.values()) for w in range(max(ws.values())+1)]
        enumerations.append({'roles':m,'width_counts':counts,'policy_count':len(ds)})
        for j in ds:
            if j==1:continue
            pos,neg=witness(j)
            assert len(pos)==len(neg)==1<<(ws[j]-1)
            assert all(d in ds for d in pos+neg)
            for k in ds:
                assert read(pos,k)-read(neg,k)==int(k==j)
                witness_checks+=1
        if m<=3:
            for length in range(4):
                for word in product(range(1<<m),repeat=length):
                    j=ideal_word(word)
                    for d in ds:
                        assert direct((d,),word)==read((d,),j)
                        word_checks+=1
        for mass in range(1, (3 if m==4 else 5)):
            t=mass.bit_length()
            groups={}
            for ledger in combinations_with_replacement(ds,mass):
                if m==4 and mass==2 and rng.randrange(5):continue
                full=tuple(read(ledger,d) for d in ds)
                short=tuple(x for x,d in zip(full,ds) if ws[d]<=t)
                assert groups.setdefault(short,full)==full
                bound_checks+=1
        for _ in range(150):
            mass=rng.randrange(1,12)
            ledger=rng.choices(ds,k=mass)
            ready={j:read(ledger,j) for j in ds if ws[j]<=mass.bit_length()}
            # The decoder never asks for the all-roles ideal: every proper
            # subquery of a proper ideal is proper.
            query=decoder(mass,ready)
            for j in ds:
                assert query(j)==read(ledger,j);codec_checks+=1
            for a in range(1<<m):
                j_a=downward(a)
                new=[d for d in ledger if sub(j_a,d)]
                for b in range(1<<m):
                    j_b=downward(b)
                    assert read(new,j_b)==read(ledger,j_a|j_b)
                    step_checks+=1
    return dict(enumerations=enumerations,word_checks=word_checks,witness_checks=witness_checks,
        codec_checks=codec_checks,bound_checks=bound_checks,step_checks=step_checks)

if __name__=='__main__':
    report=json.dumps(verify(),sort_keys=True,indent=2)+'\n'
    if len(sys.argv)>1:Path(sys.argv[1]).write_text(report)
    else:print(report,end='')
