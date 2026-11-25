from itertools import combinations, product
from pathlib import Path
from hashlib import sha1
from collections import defaultdict
import port_source

raw = Path(port_source.__file__).read_bytes()
assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == 'd896713357e80cc35f8c1fba54f6aa27af97d4ce'

# A core is a prefix-closed dictionary: each nonempty word maps to its
# last step's tests, as (coordinate, timestamp) pairs; () maps to no tests.
def lang(core, vector):
    yes = {()}
    for word, tests in sorted(core.items(), key=lambda w: len(w[0])):
        if word and word[:-1] in yes and all(vector[i] <= t for i, t in tests):
            yes.add(word)
    return frozenset(yes)

def envelope(core, yes, k, horizon):
    lo, hi = [0]*k, [horizon]*k
    clauses = []
    for word, tests in core.items():
        if word in yes:
            for i,t in tests:
                hi[i] = min(hi[i],t)
        elif word[:-1] in yes:
            assert tests
            clauses.append(tests)
            if len(tests)==1:
                i,t = tests[0]
                lo[i] = max(lo[i],t+1)
    return tuple(lo), tuple(hi), tuple(clauses)

# family of finite prefix trees with interleavings and optional branch
# labels. Any prefix downset of this test tree is included.
simple = {
    (): (),
    ('a',): ((0,0),),
    ('b',): ((1,0),),
    ('c',): (),
    ('a','b'): ((1,1),),
    ('b','a'): ((0,1),),
    ('c','c'): (),
    ('c','b'): ((1,1),),
    ('c','c','a'): ((0,2),),
    ('c','c','b'): ((1,2),),
    ('c','b','a'): ((0,2),),
    ('b','a','a'): ((0,2),),
    ('a','b','b'): ((1,2),),
}
all_vectors=list(product(range(4), repeat=2))
rest=list(simple)[1:]
boxes=hulls=extensions=0
for mask in range(1<<len(rest)):
    core={():()}
    core.update({w:simple[w] for i,w in enumerate(rest) if mask>>i&1})
    if not all(w[:-1] in core for w in core): continue
    bylang=defaultdict(set)
    for e in all_vectors:
        bylang[lang(core,e)].add(e)
    for yes,fibre in bylang.items():
        lo,hi,clauses=envelope(core,yes,2,3)
        assert lang(core,hi)==yes
        assert {e for e in all_vectors if all(a<=x<=b for a,x,b in zip(lo,e,hi))}==fibre
        assert all(all(lo[i]<=x<=hi[i] for i,x in enumerate(e)) for e in fibre)
        assert lo in fibre and hi in fibre
        boxes+=1
        # Reopening omitted base actions: old boxed evidence predicts
        # guaranteed and possible post-replacement words exactly.
        ext = [lang(simple,e) for e in fibre]
        assert set.intersection(*(set(k) for k in ext))==lang(simple,hi)
        assert set.union(*(set(k) for k in ext))==lang(simple,lo)
        extensions+=1
    hulls+=1
print(f'prefix cores {hulls}; exact serial boxes {boxes}; exact robust/possible reopening checks {extensions}')

# Atomic action providing one grant only after both verifications:
# no prefix exists after only one of its two tests.
atomic={():(),('both',):((0,0),(1,0))}
nothing=lang(atomic,(0,1))
assert nothing==lang(atomic,(1,0)) and nothing!=lang(atomic,(0,0))
lo,hi,clauses=envelope(atomic,nothing,2,1)
assert lo==(0,0) and hi==(1,1) and clauses==(((0,0),(1,0)),)
for n in range(1,13):
    # All n alternatives must individually refuse. They use disjoint
    # pairs of threshold tests; choose one blocker per pair.
    minimal = {tuple(i for b in zip((1-x for x in xs),xs) for i in b)
               for xs in product(range(2),repeat=n)}
    def refuses(e): return all(e[j] or e[j+1] for j in range(0,2*n,2))
    assert len(minimal)==2**n
    assert all(refuses(e) and all(not refuses(e[:j]+(0,)+e[j+1:]) for j,x in enumerate(e) if x)
               for e in minimal)
print('atomic rejection: one clause can have two minimal blockers, n disjoint pairs have 2^n')
# Exhaustive overlapping first-refusal clauses with Boolean thresholds.
# Each nonempty subset is a possible atomic obligation at slot zero.
atoms=[tuple((i,0) for i in range(3) if mask>>i&1) for mask in range(1,8)]
vectors=list(product(range(2),repeat=3))
qchecks=0
for mask in range(1<<len(atoms)):
    core={():(),**{(i,):ts for i,ts in enumerate(atoms) if mask>>i&1}}
    bylang=defaultdict(set)
    for e in vectors: bylang[lang(core,e)].add(e)
    for yes,fibre in bylang.items():
        _,top,clauses=envelope(core,yes,3,1)
        def keeps_refusals(e):
            return all(any(e[i]>t for i,t in c) for c in clauses)
        assert top in fibre
        for tests in [(),*atoms]:
            capped=tuple(min(top[i],*(t for j,t in tests if j==i)) if any(j==i for j,t in tests) else top[i] for i in range(3))
            assert keeps_refusals(capped)==any(all(e[i]<=t for i,t in tests) for e in fibre)
            assert all(top[i]<=t for i,t in tests)==all(all(e[i]<=t for i,t in tests) for e in fibre)
            qchecks+=1
print(f'atomic guaranteed/possible tests with overlapping refusal clauses: {qchecks}')


L,M=(1,2),(4,1)
A=(-9,-8,-5,-2)
D=(-9,-7,-5,-2)
H,W,K=8,10,4

def mode(which, word):
    # Partner's actual transfer AND a prior dispatch by A are prerequisites
    # for a change. The policy is fixed before inspecting which expiry holds.
    if which=='L':return L
    if which=='M':return M
    if which=='conditional':return M if 0 in word and 1 in word else L
    raise ValueError(which)

def native(past, which):
    init=((0,(W,)*K),(0,(W,)*K))
    for t in range(-W,0):
        edges={a:q for q,a in port_source.successors(init,((1,1,W,K//2),(1,1,W,K//2)))}
        init=edges[0 if t in past else -1]
    ls={()}; pending=[((),init)]
    while pending:
        w,st=pending.pop()
        if len(w)==H: continue
        d=mode(which,w)
        for nxt,a in port_source.successors(st,((*d,W,K//2),(1,1,W,K//2))):
            nw=w+(a,)
            ls.add(nw);pending.append((nw,nxt))
    return frozenset(ls)

def make_core(which):
    # Source-independent direct clock, disabling only initial carried tag
    # expiry tests on A. B has no old mints; later reuse on both is retained.
    core={():()}
    jobs=[((),(),())]
    while jobs:
        w,a,b=jobs.pop()
        t=len(w)
        if t==H: continue
        for act in (-1,0,1):
            aa,bb=a,b
            tests=()
            old=b if act==1 else a
            if act in (0,1):
                last=old[-1] if old else (-2 if act==0 else -W)
                d=mode(which,w)[len(a)%2] if act==0 else 1
                if t-last<d or (len(old)>=K and t-old[-K]<W):continue
                if act==0:
                    aa=a+(t,)
                    if len(a)<K:tests=((len(a),t),)
                else:
                    bb=b+(t,)
            nw=w+(act,)
            core[nw]=tests
            jobs.append((nw,aa,bb))
    return core

old={}
for which in ('L','M','conditional'):
    core=make_core(which)
    for past in (A,D):
        e=tuple(min(H,max(0,t+W)) for t in past)
        ys=lang(core,e)
        assert ys==native(past,which)
        lo,hi,_=envelope(core,ys,K,H)
        assert lang(core,hi)==ys and lang(core,lo)==ys
        old[which,past]=(ys,lo,hi)
    print(which,len(core),*(len(old[which,p][0]) for p in (A,D)),
          'lower/upper',*(old[which,p][1:] for p in (A,D)))
assert all(old[law,A]==old[law,D] for law in ('L','M'))
assert (1,0,0) in old['conditional',A][0] and (1,0,0) not in old['conditional',D][0]
assert old['conditional',A][2][1]==2 and old['conditional',D][2][1]==3
lo=tuple(max(old['L',A][1][i],old['M',A][1][i]) for i in range(K))
hi=tuple(min(old['L',A][2][i],old['M',A][2][i]) for i in range(K))
assert lo[1]==0 and hi[1]==3
assert lo[0]==hi[0]==1  # actual prior signed mint order forces second >= 2
print('fixed-law intersection second carried expiry: [2,3]; conditional switch separates at 2')
