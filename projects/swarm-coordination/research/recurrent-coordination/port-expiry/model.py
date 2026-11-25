"""Exact civil custody service model. The common port is the only clock owner."""
from itertools import product
from collections import deque
from math import gcd
from fractions import Fraction

# stream tuple is (required delay before signer 0, delay before signer 1,
# first time after a receipt that it cannot survive, tags per signer).
def period(A):
    a,b,w,M=A
    return max(M*(a+b),w)

def successors(state,params):
    for act in (-1,0,1):
        result=[]
        for j,(phase,ago) in enumerate(state):
            a,b,w,M=params[j]; cap=max(a,b,w)
            if act==j and (ago[0]<(a,b)[phase%2] or ago[-1]<w):
                break
            inc=tuple(min(cap,x+1) for x in ago)
            if act==j:result.append(((phase+1)%(2*M),(1,)+inc[:-1]))
            else:result.append((phase,inc))
        else:yield tuple(result),act

def automaton(A,B):
    init=tuple((0,(max(a,b,w),)*(2*M)) for a,b,w,M in (A,B))
    states=[init]; ids={init:0}; edges=[]
    for s in states:
        for t,act in successors(s,(A,B)):
            if t not in ids:ids[t]=len(states);states.append(t)
            edges.append((ids[s],ids[t],act))
    return states,edges

def upper_cycle_bound(states,edges,a,b,cap):
    """Find/check integer potential: scaled reward cannot exceed cap per tick."""
    scale=cap.denominator
    ew=[(u,v,scale*(a if act==0 else b if act==1 else 0)-cap.numerator,act)
        for u,v,act in edges]
    d=[0]*len(states)
    for _ in states:
        changed=False
        for u,v,w,act in ew:
            if d[v]<d[u]+w:d[v]=d[u]+w;changed=True
        if not changed:break
    else:
        return None
    assert all(d[v]>=d[u]+w for u,v,w,act in ew)
    return d,ew

def equality_witness(states, edges, a,b,cap):
    p=upper_cycle_bound(states,edges,a,b,cap)
    assert p is not None
    d,ew=p
    out=[[] for _ in states]
    for u,v,w,act in ew:
        if d[v]==d[u]+w:out[u].append((v,act))
    colour=[0]*len(states);pred={}
    def visit(s):
        colour[s]=1
        for v,act in out[s]:
            if not colour[v]:
                pred[v]=(s,act)
                q=visit(v)
                if q is not None:return q
            elif colour[v]==1:
                path=[act];u=s
                while u!=v:
                    u,k=pred[u];path.append(k)
                return path[::-1]
        colour[s]=2
        return None
    for s in range(len(states)):
        if not colour[s]:
            w=visit(s)
            if w is not None:return ''.join('AB'[act] if act>=0 else '.' for act in w)
    return None

def offsets(A,limit=None):
    a,b,w,M=A; P=period(A); K=2*M
    def gen(i,left,gaps):
        if i==K:
            if left==0:
                phase=[0]
                for d in gaps[:-1]:phase.append(phase[-1]+d)
                yield tuple(phase)
            return
        mi=(a,b)[(i+1)%2]
        tail=sum((a,b)[(q+1)%2] for q in range(i+1,K))
        for d in range(mi,left-tail+1):
            yield from gen(i+1,left-d,gaps+(d,))
    return gen(0,P,())

def phases(A,B):
    g=gcd(period(A),period(B))
    for S,T in product(offsets(A),offsets(B)):
        no={(x-y)%g for x,y in product(S,T)}
        if len(no)<g:
            return S,T,next(k for k in range(g) if k not in no)
    return None

def isolated(A,n=50):
    a,b,w,M=A; d=(a,b);K=2*M;t=[0]
    for g in range(1,n):
        t.append(max(t[-1]+d[g%2],t[g-K]+w if g>=K else 0))
    delta=max(0,w-M*(a+b))
    return all(v==(g//2)*(a+b)+(g%2)*b+(g//K)*delta for g,v in enumerate(t))

def main():
    ps=list(product(range(1,4),range(1,4),range(1,7),(1,)))
    tests=0
    for A,B in product(ps,repeat=2):
        s,e=automaton(A,B)
        assert (phases(A,B) is not None)==(equality_witness(s,e,period(A),period(B),Fraction(4)) is not None),(A,B)
        tests+=1
    sample=list(product((1,2),(1,2),(1,3,5),(1,2)))
    more=0
    for A,B in product(sample,repeat=2):
        if A[-1]+B[-1]==2:continue
        s,e=automaton(A,B)
        # Each stream at independent maximum contributes 1, with denom
        # normalized by number of local events per same-signature cycle.
        a=period(A)*B[-1];b=period(B)*A[-1]
        c=4*A[-1]*B[-1]
        assert (phases(A,B) is not None)==(equality_witness(s,e,a,b,Fraction(c)) is not None),(A,B)
        more+=1
    assert all(isolated(s) for s in product(range(1,5),range(1,5),range(1,26),range(1,7)))
    B=(1,1,6,1)
    for A in ((1,1,4,1),(1,3,4,1)):
        w=phases(A,B)
        assert (w is not None)==(A[1]==1)
        print(A,B,'same isolated rates', (Fraction(2,period(A)),Fraction(2,period(B))),'witness',w)
    print(tests,'same-port two-phase cases agree with calendar criterion')
    print(more,'cases with at least one extra tag agree with the same criterion')
    print('2400 isolated cases agree with the earliest-start closed form')

if __name__=='__main__':main()
