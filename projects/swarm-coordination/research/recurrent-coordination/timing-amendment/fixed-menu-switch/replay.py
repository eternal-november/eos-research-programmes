from itertools import combinations
from random import Random
from hashlib import sha1
from pathlib import Path
import port_source

source=Path(port_source.__file__).read_bytes()
assert sha1(f'blob {len(source)}\0'.encode()+source).hexdigest()=="d896713357e80cc35f8c1fba54f6aa27af97d4ce"
L=(1,2); M=(4,1)
A=(-9,-8,-5,-2); B=(-9,-7,-5,-2)
W=10; K=4; H=12

def mint_protocol(past, word, k, w, law, end):
    """Pinned port successor; simulate one active scope and an idle peer."""
    start=past[0]
    state=((0,(w,)*k),(0,(w,)*k))
    for t in range(start,end):
        a=0 if t in (past if t<0 else word) else -1
        d=(1,1) if t<0 else law(t)
        sub=(d[0],d[1],w,k//2)
        edges=dict((act,new) for new,act in port_source.successors(state,(sub,sub)))
        if a not in edges:return False
        state=edges[a]
    return True

def direct(past, word, k, w, law):
    if not word:return True
    ts=past+word
    for i,t in enumerate(ts):
        d=(1,1) if t<0 else law(t)
        if i and t-ts[i-1]<d[i%2]:return False
        if i>=k and t-ts[i-k]<w:return False
    return True

def greedy(past,k,w,law,H):
    z=[];t=past[-1]
    for i,q in enumerate(past):
        e=q+w
        t=next((c for c in range(max(0,e,t+1),H) if c-t>=law(c)[i%2]),H)
        z.append(t)
    return tuple(z)

def sweep(past,w,calendar,H):
    # Calendar is a sorted sequence of half-open intervals (start,end,pair).
    j=0; t=past[-1]; out=[]
    for i,mint in enumerate(past):
        e=max(0,mint+w)
        while j<len(calendar):
            a,b,d=calendar[j]
            u=max(a,e,t+d[i%2])
            if u<b:
                t=u;break
            j+=1
        else:t=H
        out.append(t)
    return tuple(out)

def admitted(word,last,p,w,law):
    K=len(p)
    for i,t in enumerate(word):
        if t-(last if i==0 else word[i-1])<law(t)[i%2]:return False
        if i<K and t<p[i]:return False
        if i>=K and t-word[i-K]<w:return False
    return True

def subs(H):
    return (s for i in range(H+1) for s in combinations(range(H),i))

laws=(lambda t:L,lambda t:M,lambda t:L if t<=1 else M)
alls=[]
for j,law in enumerate(laws):
    hist=[]
    for prior in (A,B):
        assert mint_protocol(prior,(),K,W,law,0)
        profile=greedy(prior,K,W,law,H)
        assert profile==sweep(prior,W,([(0,H,L),(0,H,M)][j:j+1] if j<2 else [(0,2,L),(2,H,M)]),H)
        expected=((1,3,5,8),(2,3,7,8),(1,2,6,8) if prior==A else (1,3,7,8))
        assert profile==expected[j],(profile,expected)
        ws=set()
        for s in subs(H):
            b=direct(prior,s,K,W,law)
            assert b==mint_protocol(prior,s,K,W,law,H)
            assert b==admitted(s,prior[-1],profile,W,law)
            if b:ws.add(s)
        hist.append(ws)
    diff=sorted(hist[0]^hist[1],key=lambda s:(len(s),s))
    assert (not diff) if j<2 else diff and diff[0]==(1,2)
    alls.append(tuple(len(z) for z in hist))
assert alls==[(321,321),(126,126),(192,171)],alls
# Same local observation gives the robust intersection. A certified due
# bit for the second old mint separates the two attainable fibres.
assert direct(A,(1,2),K,W,laws[2]) and not direct(B,(1,2),K,W,laws[2])
assert not all(direct(p,(1,2),K,W,laws[2]) for p in (A,B))
assert all(direct(p,(1,2),K,W,laws[2]) for p in (A,B) if p[1]+W<=2)

rng=Random(384391); extra=0
for h in range(1,10):
    for k in (2,4,6):
        for run in range(20):
            p=tuple(sorted(rng.sample(range(-18,0),k)))
            w=rng.randrange(1,11)
            cal=[tuple(rng.randrange(1,6) for _ in range(2)) for t in range(h)]
            law=cal.__getitem__
            E=greedy(p,k,w,law,h)
            assert E==sweep(p,w,[(t,t+1,x) for t,x in enumerate(cal)],h)
            words=set()
            for s in subs(h):
                a=admitted(s,p[-1],E,w,law)
                assert a==direct(p,s,k,w,law)
                if a:words.add(s)
                extra+=1
            for i,e in enumerate(E):
                assert (e==h or E[:i+1] in words)
                assert e==min((x[i] for x in words if len(x)>i),default=h)
print(f'whole_menu_and_switch_checks={6*2**H} counts_by_law={alls} earliest_split=(1,2)')
print(f'calendar_profile_checks={extra} identical_before_switch=True qualified_due_bit_suffices=True')
