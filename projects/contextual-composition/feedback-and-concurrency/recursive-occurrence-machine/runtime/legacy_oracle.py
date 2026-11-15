"""Independent structural big-step oracle for the finite phase fragment.

Not implemented by running the small-step machine. Callback tables remain trusted
primitive parameters; no arbitrary recursive/concurrent terms accepted here.
"""
from dataclasses import dataclass
from copy import deepcopy
from fractions import Fraction
from occurrence_machine import Leaf, Node, Ret, Op, Bind, Batch, Case, graft, leaves

@dataclass
class Evaluation:
    tree: object
    raw: object
    weight: Fraction
    cost: tuple
    word: tuple
    world: object
    stores: dict


def evaluate(term, value, caps, primitives, choose, world=None, stores=None, dimension=1):
    world=deepcopy({} if world is None else world)
    stores=deepcopy(stores or {})
    if isinstance(term,Ret):
        return Evaluation(Leaf(term.f(value),tuple(sorted(caps))),('ret',),Fraction(1),(0,)*dimension,(),world,stores)
    if isinstance(term,Op):
        alternatives=primitives[term.name](term.arg(value),tuple(sorted(caps)),deepcopy(world),{c:deepcopy(stores[c]) for c in caps if c in stores})
        ai,oi=choose(term.name)
        o=alternatives[ai][oi]
        stores.update(deepcopy(o.stores))
        return Evaluation(o.tree,('op',term.name,ai,oi,o.witness),o.weight,o.cost,(o.event,),deepcopy(o.world),stores)
    if isinstance(term,Case):
        return evaluate(term.terms[term.select(value)],value,caps,primitives,choose,world,stores,dimension)
    if isinstance(term,Bind):
        left=evaluate(term.left,value,caps,primitives,choose,world,stores,dimension)
        rs=[];world=left.world;stores=left.stores
        for leaf in leaves(left.tree):
            r=evaluate(term.k(leaf.value),leaf.value,leaf.caps,primitives,choose,world,stores,dimension)
            rs.append(r);world=r.world;stores=r.stores
        weight=left.weight
        for r in rs:weight*=r.weight
        return Evaluation(graft(left.tree,[r.tree for r in rs]),('bind',left.raw,tuple(r.raw for r in rs)),weight,
            tuple(left.cost[i]+sum(r.cost[i] for r in rs) for i in range(dimension)),
            left.word+tuple(x for r in rs for x in r.word),world,stores)
    if isinstance(term,Batch):
        rs=[]
        for child,data,bundle in term.split(value,tuple(sorted(caps))):
            r=evaluate(child,data,bundle,primitives,choose,world,stores,dimension)
            rs.append(r);world=r.world;stores=r.stores
        weight=Fraction(1)
        for r in rs:weight*=r.weight
        return Evaluation(Node('Fork',tuple(r.tree for r in rs),True),('batch',tuple(r.raw for r in rs)),weight,
            tuple(sum(r.cost[i] for r in rs) for i in range(dimension)),tuple(x for r in rs for x in r.word),world,stores)
    raise TypeError('outside finite legacy oracle fragment: '+type(term).__name__)
