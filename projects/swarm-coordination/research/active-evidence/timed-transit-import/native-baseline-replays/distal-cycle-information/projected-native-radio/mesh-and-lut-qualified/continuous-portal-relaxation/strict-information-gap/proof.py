"""Proof checker: finite portal-chain lower bounds with exact integer duals."""
import sys,json
from pathlib import Path
from itertools import pairwise
import lower
Q=10**7

def pths(E,a,b,halt=()):
    adj={i:[] for i in lower.I}
    for u,v in sorted(E):adj[u].append(v);adj[v].append(u)
    def gen(xs):
        v=xs[-1]
        if v==b:yield xs
        elif v not in halt:
            for u in adj[v]:
                if u not in xs:yield from gen(xs+(u,))
    return gen((a,))

def tasks(P):
    E=set(P)
    S=lower.point(lower.S);G=lower.point(lower.G);K=sorted(lower.K)
    stops={t for edge in K for t in edge}
    proof={}
    known={}
    local={}
    def ports(p):return [P[tuple(sorted(e))] for e in pairwise(p)]
    def add(k,boxes):
        assert k not in proof
        proof[k]=boxes
        return k
    for i,e in enumerate(K):
        known[i]=[add(f"k/{i}/"+",".join(map(str,p)),[S,*ports(p),G])
                   for p in pths(E-{e},103,132)]
    for obs in sorted(stops):
       for p in pths(E-set(K),103,obs,stops):
          assert len(p)>1
          key=",".join(map(str,p))
          local[key]={}
          for i,e in enumerate(K):
             local[key][i]=[add(f"o/{key}/{i}/"+",".join(map(str,s)),
                                [S,*ports(p),*ports(s),G])
                            for s in pths(E-{e},obs,132)]
    assert set(local)=={"103,104,108,116,117","103,105,106,107,118"}
    assert all(known.values()) and all(v[i] for v in local.values() for i in (0,1))
    return proof,known,local

def valid(box,vectors):
    n=len(box)
    assert len(vectors)==n-1
    for u in vectors:
        assert len(u)==3 and all(type(x) is int for x in u)
        assert sum(x*x for x in u)<=Q*Q
    z=(0,0,0)
    coeff=[tuple(a-b for a,b in zip(u,v))
           for u,v in zip([z,*vectors],[*vectors,z])]
    score=0
    for c,(lo,hi) in zip(coeff,box):
        for k,a,b in zip(c,lo,hi):
            score+=k*int(a if k>=0 else b)
    return score

def main():
    A,lo,n=lower.bulk();_,P=lower.adjacent(A,lo)
    proof,known,local=tasks(P)
    lines=json.loads(Path(sys.argv[2]).read_text())
    assert set(lines)==set(proof)
    scores={k:valid(box,lines[k]) for k,box in proof.items()}
    k={i:min(scores[a] for a in chain) for i,chain in known.items()}
    observed={p:[k[i]+min(scores[a] for a in vs[i]) for i in (0,1)]
              for p,vs in local.items()}
    bound=min(max(c) for c in observed.values())
    assert bound>0
    print(json.dumps(dict(dual_denominator=2*Q,known=[2*k[i] for i in (0,1)],
        local_lower=bound,observed=observed,checked=len(scores)),sort_keys=True))
if __name__=="__main__":main()
