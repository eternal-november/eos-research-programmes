"""Exact transport and charged diagnosis in a two-stage forecast model."""
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache
import json

HALF=Q(1,2)
CLIP=lambda x:min(Q(1),max(Q(0),x))
BITS=(0,1)
def probs(p):
    return {(x,x^z):HALF*(p if z else 1-p) for x,z in product(BITS,repeat=2)}
def read(p,index):
    return tuple(sum(w for h,w in probs(p).items() if h[index]==x) for x in BITS)
def channel(q0,q1,eps):
    # z -> outcomes labeled absent, reported zero, reported one.
    return ((1-q0,q0*(1-eps),q0*eps),(1-q1,q1*eps,q1*(1-eps)))
def law(p,chan):
    return tuple((1-p)*a+p*b for a,b in zip(*chan))
def parity_channel_direct(p,q0,q1,eps):
    counts=[Q(0)]*3
    for (x,y),w in probs(p).items():
        z=x^y
        q=q0 if not z else q1
        for available,flip in product(BITS,repeat=2):
            likelihood=(q if available else 1-q)*(eps if flip else 1-eps)
            k=(z^flip)+1 if available else 0
            counts[k]+=w*likelihood
    return tuple(counts)

def regret_interval(lo,hi):
    # Action 1 serves if Z=1, action 0 if Z=0. For all p, regret is
    # minimized before cause is learned by mixing between the two actions.
    left,right=max(Q(0),1-2*lo),max(Q(0),2*hi-1)
    if left+right==0:return HALF,Q(0)
    return right/(left+right),left*right/(left+right)

def vertex_minimax(points):
    # Convex hull of deterministic terminal choices. Leading coordinate is
    # error under the lower-p law; trailing one under the higher-p law.
    best=min(max(x) for x in points)
    for p,q in product(points,repeat=2):
        d=p[0]-p[1]
        e=q[0]-q[1]
        if d*e<0:
            lam=e/(e-d)
            value=lam*p[0]+(1-lam)*q[0]
            assert value==lam*p[1]+(1-lam)*q[1]
            best=min(best,value)
    return best

def policy_points(a,b):
    return tuple((sum(x for y,x in zip(rule,a) if y),
                  sum(x for y,x in zip(rule,b) if not y))
                 for rule in product(BITS,repeat=len(a)))

def bayes_equal(a,b):
    return sum(min(x,y) for x,y in zip(a,b))/2

def direct_grid(p0,p1,eps,erasure):
    # Explicit binary experiment policies: click or skip, then four
    # possible response tuples at each naive parity read, including loss.
    ch=channel(1-erasure,1-erasure,eps)
    a=parity_channel_direct(p0,*((1-erasure,)*2),eps)
    b=parity_channel_direct(p1,*((1-erasure,)*2),eps)
    assert (a,b)==(law(p0,ch),law(p1,ch))
    return vertex_minimax(policy_points(a,b))

def protected_dp(gap,eps,drop,cost,horizon):
    z=gap*(1-2*eps)
    plus=(drop,(1-drop)*(HALF-z),(1-drop)*(HALF+z))
    minus=(plus[0],plus[2],plus[1])
    delta=2*gap
    @lru_cache(None)
    def opt(n,post):
        stop=delta*min(post,1-post)
        if n==0:return stop
        nxt=cost
        for a,b in zip(plus,minus):
            j=post*a+(1-post)*b
            if j:nxt+=j*opt(n-1,post*a/j)
        return min(stop,nxt)
    def fixed(n):
        value=n*cost
        for seq in product(range(3),repeat=n):
            pos=neg=Q(1)
            for k in seq:
                pos*=plus[k]
                neg*=minus[k]
            value+=delta*HALF*min(pos,neg)
        return value
    return opt(horizon,HALF),[fixed(n) for n in range(horizon+1)]

def direct_stopping(gap,eps,drop,cost,H):
    g=gap*(1-2*eps)
    a=(drop,(1-drop)*(HALF+g),(1-drop)*(HALF-g))
    b=(a[0],a[2],a[1])
    def raw(n,wa,wb):
        stop=2*gap*min(wa,wb)
        return min(stop,cost*(wa+wb)+sum(raw(n-1,wa*x,wb*y)
            for x,y in zip(a,b))) if n else stop
    return raw(H,HALF,HALF)

def main():
    vals=tuple(Q(i,16) for i in range(17))
    shifts=0
    for observed,delta in product(vals,repeat=2):
        lo,hi=CLIP(observed-delta),CLIP(observed+delta)
        l,r=regret_interval(lo,hi)
        brute=vertex_minimax(((Q(0),max(Q(0),2*hi-1)),(max(Q(0),1-2*lo),Q(0))))
        assert r==brute
        for p in vals+(lo,hi):
            if lo<=p<=hi:
                assert read(p,0)==read(p,1)==(HALF,HALF)
                assert max(l*(1-2*p),(1-l)*(2*p-1))<=r
        assert max(l*(1-2*lo),(1-l)*(2*hi-1))==r
        shifts+=1
    symmetric=0
    for gap,eps,erasure in product(vals[:9],vals[:9],vals):
        exp=HALF-gap*(1-2*eps)*(1-erasure)
        assert direct_grid(HALF-gap,HALF+gap,eps,erasure)==exp
        symmetric+=1
    # Same probed-fault pair, but an asymmetric channel. An unsupported
    # unconditional discard of "absent" loses likelihood information.
    gap=Q(1,4)
    p0,p1=HALF-gap,HALF+gap
    cases={}
    for name,ch in (
         ('perfect',channel(Q(1),Q(1),0)),
         ('half-erased',channel(HALF,HALF,0)),
         ('selection-only',channel(0,1,HALF)),
         ('unsymmetrical',channel(Q(1,8),Q(1,4),Q(1,8)))):
        a,b=law(p0,ch),law(p1,ch)
        best=vertex_minimax(policy_points(a,b))
        bayes=bayes_equal(a,b)
        assert best>=bayes
        cases[name]=[str(best),str(bayes),str(2*gap*(HALF-best))]
    assert cases['perfect'][0]=='1/4'
    assert cases['half-erased'][0]=='3/8'
    assert cases['selection-only'][0]=='1/4'
    assert cases['unsymmetrical'][0]!=cases['unsymmetrical'][1]
    checked=0
    for a,e,d,c,H in product((Q(1,8),Q(1,4),Q(1,2)),(0,Q(1,8),HALF),
                (0,Q(1,3),1),(0,Q(1,128),Q(1,16)),range(5)):
        adaptive,fixed=protected_dp(a,e,d,c,H)
        assert adaptive==direct_stopping(a,e,d,c,H) and adaptive<=min(fixed)
        checked+=1
    adaptive,fixed=protected_dp(Q(1,4),0,Q(1,3),Q(1,64),5)
    assert adaptive<min(fixed)
    print(json.dumps(dict(shift_controls=shifts,symmetric_exact=symmetric,
        examples=cases,stopping_checks=checked,
        adaptive_stopping=[str(adaptive),str(min(fixed)),[str(x) for x in fixed]],
        unload_joint_pair={'law_minus':'1/2','law_plus':'1/2'},
        loaded_marginals=['1/2','1/2'],different_reserve=['0','1']),
        sort_keys=True,indent=2))
if __name__=='__main__':main()
