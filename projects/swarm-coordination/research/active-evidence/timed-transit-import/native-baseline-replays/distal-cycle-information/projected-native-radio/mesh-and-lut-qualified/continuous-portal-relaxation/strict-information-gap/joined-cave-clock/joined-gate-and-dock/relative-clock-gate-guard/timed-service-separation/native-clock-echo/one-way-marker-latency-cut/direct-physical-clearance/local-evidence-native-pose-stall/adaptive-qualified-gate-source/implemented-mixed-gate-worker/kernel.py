"""Finite operational sketch, specified independently of the native store.

Scope: one stable duty key, evidence already qualifies by shape/gate/
era and has no expiry in this slice. Public observations include exact
immutable receipts (time is a symbolic event serial), not SQL internals.
"""
from dataclasses import dataclass,replace
from itertools import product

@dataclass(frozen=True)
class Context:
    holder:int=10
    # Permission to inspect historical Q is separately fixed for both
    # actors; neither gains the other actor's permission to install.
    def permits(self,actor): return self.holder==actor and actor!=0

@dataclass(frozen=True)
class Content:
    witnesses:int=0 # independently qualified optical (1), radio (2)
    receipt:tuple|None=None # (result, at, actual effect actor or 0)
    def clear(self):return bool(self.witnesses)

@dataclass(frozen=True)
class State:
    law:Context=Context()
    facts:Content=Content()

def step(s,action,t):
    k,v=action
    if k=='attest':
        return replace(s,facts=replace(s.facts,witnesses=s.facts.witnesses|v)),('recorded',)
    if k=='handoff':
        assert s.law.holder==10 and v in (0,11)
        return replace(s,law=Context(v)),('transferred',)
    if k=='inspect':
        assert v in (10,11)
        return s,('historical',s.facts.receipt)
    assert k=='apply' and v in (10,11)
    # Typed disjoint union: a past receipt and a newly authorized effect
    # are not two interchangeable terms in the same admission fiber.
    if s.facts.receipt is not None:
        return s,('historical',s.facts.receipt)
    if not s.law.permits(v):
        return s,('stale',)
    receipt=('closed' if s.facts.clear() else 'blocked',t,v if s.facts.clear() else 0)
    return replace(s,facts=replace(s.facts,receipt=receipt)),('fresh',receipt)

def run(steps,s=State()):
    y=[]
    for i,a in enumerate(steps,1):
        s,o=step(s,a,i);y.append(o)
    return s,y

def legal(s,cut,actor):
    # Native boundary observation; a client can query fresh enablement
    # only while the obligation is still unsettled, not conflated with
    # a successful historical replay.
    current= s.law.permits(actor)
    matches=s.facts.clear()
    return s.facts.receipt is None and current and matches

def section(s,include_audit=False):
    # Relative-profile test family over all actual downstream actors.
    # Fixed receipt query requires exact time and result.
    # Factor values can be represented in a separate audit client.
    main=(s.facts.receipt,tuple(legal(s,None,a) for a in (10,11)))
    return (*main,s.facts.witnesses) if include_audit else main

def profiles():
    # Find exact obstruction pairs to common factor descent for evidence
    # or actor forgetting. Equal-content fibers need not agree downstream.
    s=State(Context(10),Content(1))
    n=replace(s,law=Context(11))
    assert s.facts==n.facts and section(s)!=section(n)
    r=replace(s,facts=Content(2))
    assert section(r)==section(s) and section(r,True)!=section(s,True)
    occupied=replace(s,facts=Content(1,('closed',9,10)))
    # Read commutes with the context-side authority change.
    t,_=step(occupied,('handoff',11),10)
    assert step(occupied,('inspect',10),11)[1]==step(t,('inspect',10),11)[1]
    # New actuation cannot commute past that context-side change.
    w,x=run([('apply',10),('handoff',11)],s)
    y,z=run([('handoff',11),('apply',10)],s)
    assert w.facts.receipt==('closed',1,10) and y.facts.receipt is None
    assert x[0][0]=='fresh' and z[1]==('stale',)
    # An independently authenticated observation can move through
    # the context change unchanged; this is a native opt-in premise.
    for op,x in product((('attest',1),('attest',2)),(0,11)):
        before=run([op,('handoff',x)])[0]
        after=run([('handoff',x),op])[0]
        assert before==after
profiles()
