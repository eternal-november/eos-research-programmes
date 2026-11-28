from brake import minimum,step
from itertools import product

def policy(v,d,which,e):
    # e indexes the world in this replay. The controller gets it only
    # when the delivered execution receipt identifies it.
    n=2*v
    balanced=(1,-1,-1,1)*(v//2)+(1,-1)*(v%2)
    if which=='slow-extreme':
        base=(1,)*v+(-1,)*v
    elif which=='slow-next':
        base=(-1,)+(1,)*v+(-1,)*(v-1)
    elif which=='bounded':
        u=v-d
        base=(1,-1,-1,1)*(u//2)+(1,-1)*(u%2)+(1,)*d+(-1,)*d
    else:
        base=balanced
    xs=(v,v,0)
    acts=[]
    suffix={}
    worst=0
    for t in range(n+1):
        known=(e if 0<=e<n and e+d+1<=t else None)
        if t in suffix:
            a=suffix[t]
        elif which=='slow-extreme':
            a=base[t] if t<n else (base[known] if known is not None else -1)
        elif which=='slow-next':
            if known==0:
                assert t>=v
                a=-1 if t<2*v else 1
            else:
                a=base[t] if t<n else (base[known] if known is not None else -1)
        elif which in ('now','bounded'):
            if known is None:
                a=base[t] if t<n else (-1 if which=='bounded' else 0)
            else:
                k=e+d+1
                a=base[known] if t==k else base[t-1]
        elif which=='lag-one':
            if known is None:
                a=base[t] if t<n else base[-1]
            else:
                assert t==known+2
                comp=[base[known]]
                if known%2:comp.append(-base[known])
                # At the first receipt the controller can reconstruct
                # state from its known commands and the single named omission.
                reconstruction=(v,v,0)
                for u,a0 in enumerate(acts):
                    reconstruction=step(reconstruction,a0,known==u,True)
                for a0 in comp:reconstruction=step(reconstruction,a0,False,True)
                p,f,g=reconstruction
                assert p==f
                for _ in range(p):
                    a0=-1 if g>=0 else 1
                    comp.extend((a0,-a0));g+=2*a0
                assert t+len(comp)==n+1
                suffix=dict(enumerate(comp,t))
                a=suffix[t]
        else:raise ValueError(which)
        prev=xs
        xs=step(xs,a,e==t,which!='now')
        assert xs is not None,(v,d,which,e,t,prev,a)
        worst=max(worst,abs(xs[2]))
        acts.append(a)
    assert xs[:2]==(0,0),(which,v,d,e,acts,xs)
    return acts,worst

def test_policy(v,d,which,expected,exact):
    obs={}
    high=0
    for e in range(-1,2*v+1):
        out,cap=policy(v,d,which,e)
        high=max(high,cap)
        for t,a in enumerate(out):
            val=e if 0<=e<2*v and e+d+1<=t else -1
            key=(t,val)
            assert obs.setdefault(key,a)==a
    assert high<=expected,(v,d,which,expected,high)
    if exact:assert high==expected
    return 2*v+2


def blind(v):
    seq=(1,-1,-1,1)*(v//2)+(1,-1)*(v%2)+(1,-1)
    H=len(seq)
    assert H==2*v+2
    finals={}
    for e in range(-1,H):
        state=(v,v,0);peak=0
        for t,a in enumerate(seq):
            state=step(state,a,t==e,True);peak=max(peak,abs(state[2]))
        assert state[:2]==(0,0) and peak<=2*(2*v+2)
        finals[e]=state[2]
    for a in (-1,1):
        loc=[i for i,s in enumerate(seq) if s==a]
        assert len(loc)==v+1
        assert finals[loc[0]]-finals[-1]==-2*a*(loc[-1]-loc[0])
    return H+1

def main():
    number=0
    for v in range(1,50):
        number+=test_policy(v,0,'now',4,True)
        number+=test_policy(v,1,'lag-one',4,True)
        number+=test_policy(v,v,'slow-extreme',2*(v*v+v),True)
        if v>=3:number+=test_policy(v,v-1,'slow-next',2*(v*v-v-1),True)
        for d in (1,(v+1)//2,v):
            number+=test_policy(v,d,'bounded',2*(d*d+2*d+2),False)
    blind_traces=sum(blind(v) for v in range(1,80))
    for v in range(1,7):
        n=2*v+1
        t=[minimum(v,d,n) for d in range(v+2)]
        assert t[:2]==[4,4] and t[v]==2*(v*v+v) and t[-1] is None
        if v>=3:assert t[v-1]==2*(v*v-v-1)
        for d,c in enumerate(t[:-1]):
            assert 2*c>=d*d+2*d and c<=2*(d*d+2*d+2)
        assert minimum(v,0,n,False)==4
        assert all(minimum(v,d,n,False) is None for d in range(1,v+2))
        print('v',v,'exact minimum doubled half-band by delay',t)
    print(number,'named-world constructive traces; identical-observation choices matched')
    print(blind_traces,'blind two-spare-slot trajectories and exact signed area shifts')
if __name__=='__main__':main()
