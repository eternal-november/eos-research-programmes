"""Small declared slotted plant; finite graph compiled from total row semantics."""
from dataclasses import dataclass
from itertools import product
from reuse import Graph,Edits,Fact

@dataclass(frozen=True)
class Mode:
    # The binding is fixed for an entire run, not reselected at each edge.
    shared_diagnostic_pool: bool
    slow_diagnostic: bool=False

@dataclass(frozen=True)
class S:
    t: int
    units: int
    movement: str
    pickup: bool

states=tuple(S(t,r,o,p) for t,r,o,p in product(
    range(5),(0,1),('pending','retired','inside','left'),(False,True)))

def id(s):
    return ':'.join(map(str,(s.t,s.units,s.movement,int(s.pickup))))

def step(mode,s):
    t,r,m,p=s.t,s.units,s.movement,s.pickup
    if t==4:return s
    if t==0:
        if mode.shared_diagnostic_pool:r=max(0,r-1)
    elif t==1:
        if r and m=='pending':
            r-=1;m='retired'  # effect completion, not a reported request
    elif t==2:
        if m=='pending':m='inside'
        if not mode.slow_diagnostic:p=True
    elif t==3 and m=='inside':
        m='left'
    return S(t+1,r,m,p)

def compile(mode):
    out={id(s):frozenset({id(step(mode,s))}) for s in states}
    facts={id(s):Fact(frozenset(
        {name for name,condition in [
            ('safety', s.t==3 and s.movement=='inside'),
            ('deadline', s.t==3 and not s.pickup)] if condition})) for s in states}
    init=S(0,1,'pending',False)
    return Graph(frozenset({id(init)}),out,facts)

def patch(g,new):
    # Transparent producer; this v0 reads every row to form a complete edit.
    return Edits(roots=None if g.roots==new.roots else new.roots,
                 out={i:new.out[i] for i in g.out if g.out[i]!=new.out[i]},
                 facts={i:new.facts[i] for i in g.facts if g.facts[i]!=new.facts[i]})
