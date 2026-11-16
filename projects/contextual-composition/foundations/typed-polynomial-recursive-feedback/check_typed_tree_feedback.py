"""Finite diagnostics, not a proof of the general categorical statements."""
from functools import lru_cache
from itertools import product
from fractions import Fraction as Q
import json

# Node=(shape, children); child is None (external leaf) or (colour, Node).
ARITY={"z":0,"u":1,"b":2}

def node_count(t):
    return 1+sum(node_count(c[1]) for c in t[1] if c is not None)

@lru_cache(None)
def trees(n):
    out=[]
    for shape,k in ARITY.items():
        if k==0:
            if n==1: out.append((shape,()))
            continue
        # distribute n-1 nodes among k slots, zero meaning external leaf.
        for sizes in product(range(n),repeat=k):
            if sum(sizes)!=n-1: continue
            options=[]
            for m in sizes:
                options.append([None] if m==0 else [(col,t) for col in ('U','V') for t in trees(m)])
            out.extend((shape,tuple(cs)) for cs in product(*options))
    return tuple(out)

def split(t):
    """Cut U edges: outer U tree of nonempty inner V trees."""
    outer=[]
    def block(t):
        cs=[]
        for c in t[1]:
            if c is None:
                cs.append(None); outer.append(None)
            elif c[0]=='U':
                cs.append(None); outer.append(('U',split(c[1])))
            else:
                cs.append(('V',block(c[1])))
        return (t[0],tuple(cs))
    inner=block(t)
    return (inner,tuple(outer))

def flatten(m):
    children=iter(m[1])
    def fill(t):
        cs=[]
        for c in t[1]:
            if c is None:
                outer=next(children)
                cs.append(None if outer is None else ('U',flatten(outer[1])))
            else:
                cs.append(('V',fill(c[1])))
        return (t[0],tuple(cs))
    t=fill(m[0])
    assert next(children,'END')=='END'
    return t

counts={}
for n in range(1,5):
    ts=trees(n); counts[n]=len(ts)
    for t in ts:
        m=split(t)
        assert flatten(m)==t
        assert split(flatten(m))==m
        assert node_count(flatten(m))==n

# Branching execution: nullary terminal with p=1/3, binary recursion q=2/3.
# Height truncation is monotone, bounded by 1/2, and converges to the smaller
# root of q=p+(2/3)q^2. This finite check is not the limit proof.
p,q=Q(1,3),Q(2,3)
mass=Q(0); masses=[]
for h in range(1,8):
    nxt=p+q*mass*mass
    assert mass<=nxt<=Q(1,2)
    mass=nxt
    masses.append({'height':h,'mass_exact':str(mass),'mass_decimal':float(mass)})
assert p+q*Q(1,2)**2==Q(1,2)
assert p+q*Q(1)**2==Q(1)

# A native scalar aggregation splits the terminal witness into two witnesses.
# Root-wise and child-wise finite Fubini recover every target tree weight.
split_terminal=(Q(1,9),Q(2,9))
assert sum(split_terminal)==p
for n_term in range(1,6):
    summed=sum((__import__('functools').reduce(lambda a,b:a*b,ws,Q(1))
                for ws in product(split_terminal,repeat=n_term)),Q(0))
    assert summed==p**n_term

# Fixed shared seed versus resampled sibling seeds on immediate termination.
pterm=Q(1,3)
shared_unequal=Q(0)
resampled_unequal=sum((Q(1,4)*pterm*pterm for a,b in product((0,1),repeat=2) if a!=b),Q(0))
assert resampled_unequal==pterm*pterm/2==Q(1,18)

print(json.dumps({'shared_seed_unequal_mass':str(shared_unequal),
                  'resampled_seed_unequal_mass':str(resampled_unequal),
                  'shape_counts':counts,'all_coloured_tree_roundtrips':'passed',
                  'termination_height_masses':masses,
                  'finite_scalar_aggregation':'passed',
                  'scope':'finite diagnostics only; no categorical or limit proof'},indent=2))
