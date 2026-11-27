"""Exact time-qualified receipt reuse: no forged signatures or remote system."""
from itertools import product
from random import Random
import json
import paced

def alive(expiry,start,inclusive):
    return expiry>=start if inclusive else expiry>start

def arc(a,b,profile,P,U,inclusive):
    si,_,end=profile[a%len(profile)]
    sj,start,_=profile[b%len(profile)]
    if si!=sj:
        return False
    return alive(a*P+end+U,b*P+start,inclusive)

def direct_arcs(profile,n,P,U,inclusive):
    # Independent integer semantics: old emission at any allowed slot,
    # fresh singleton can appear at any allowed slot, network retention
    # delay bounded by the age law. All starts saturated here.
    out=set()
    for j in range(n):
      s,c,d=profile[j%len(profile)]
      for i in range(j):
        t,a,b=profile[i%len(profile)]
        if s!=t:continue
        observed_fresh=set(range(j*P+c,j*P+d+1))
        observed_old={i*P+e+lag for e in range(a,b+1)
                      for lag in range(U+int(inclusive))}
        if observed_fresh & observed_old:out.add((i,j))
    return out

def tag_count(profile,P,U,inclusive):
    assert all(0<=f<=b<=P for s,f,b in profile)
    L=max(0,(U+max(x[2] for x in profile)-min(x[1] for x in profile))//P)
    N=len(profile)
    # One complete target cycle with full predecessor history.
    return max(1+sum(arc(k,i,profile,P,U,inclusive)
                     for k in range(i-L,i)) for i in range(L,L+N))

def greedy(profile,n,P,U,inclusive):
    tags=[]
    for j in range(n):
        unavailable={tags[i] for i in range(j) if arc(i,j,profile,P,U,inclusive)}
        tags.append(next(v for v in range(n) if v not in unavailable))
    return tags

def brute_coloring(n,edges):
    prev={}
    att={i:set() for i in range(n)}
    for i,j in edges:att[j].add(i)
    def visit(j,m):
        if j==n:return True
        for k in range(m):
            if all(prev[i]!=k for i in att[j]):
                prev[j]=k
                if visit(j+1,m):return True
                prev.pop(j)
        return False
    return next(m for m in range(1,n+1) if visit(0,m))

def commissioning(exact):
    # Busy interface g=P=4. A and B are distinct authorized categories
    # chosen at an authenticated local boundary; the pipeline otherwise
    # requires unchanged physical setup and actual settlement checks.
    P=g=4;U=6
    fast=((0,1,3),(1,1,3))
    paired=((0,1,1),(1,3,3))
    if not exact:
        paired=fast  # replacement preserves coarse time and signer set
    profile={0:((0,2,2),),2:fast,3:paired}
    need={i:tag_count(x,P,U,True) for i,x in profile.items()}
    # The first link has its own two-value tag capability. Second link
    # has one tag value, and can use mode 2 or 3.
    avail=((0,),tuple(x for x in (2,3) if need[x]<=1))
    assert paced.synth(avail,g,P)==((0,3) if exact else None)
    return need

def main():
    rng=Random(91023)
    tables=0;colors=0
    for _ in range(1100):
        P=rng.randint(2,8)
        U=rng.randint(0,3*P)
        n=rng.randint(1,4)
        profile=tuple((rng.randrange(3),a,rng.randint(a,P))
                      for a in (rng.randrange(P) for i in range(n)))
        for inc in (False,True):
            N=6
            es=direct_arcs(profile,N,P,U,inc)
            assert es=={(i,j) for i in range(N) for j in range(i+1,N)
                        if arc(i,j,profile,P,U,inc)}
            assert max(greedy(profile,N,P,U,inc))+1==brute_coloring(N,es)
            tables+=1
            # Run a span long enough to visit every steady-state phase.
            fixed=tag_count(profile,P,U,inc)
            assert fixed==max(greedy(profile,2*n+8,P,U,inc))+1
            colors+=1
    # Earlier arrival creates an equality at the age cut of 6,
    # for the same signer in uses zero and two (P=4).
    f=((0,1,3),(1,1,3))
    shifted=((0,2,3),(1,2,3))
    assert tag_count(f,4,6,True)==2
    assert tag_count(f,4,6,False)==1
    assert tag_count(shifted,4,6,True)==1
    assert tag_count(f,5,6,True)==1
    assert commissioning(True)=={0:2,2:2,3:1}
    assert commissioning(False)=={0:2,2:2,3:2}
    print(json.dumps(dict(age_edge_tables=tables,colored_periods=colors,
                          relative_earliest_shift=[2,1],equality_convention=[2,1],
                          commissioned=[commissioning(True),commissioning(False)]),
                     indent=2,sort_keys=True))

if __name__=="__main__":main()
