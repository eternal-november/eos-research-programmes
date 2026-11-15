"""Finite ranked-template adapter; trusted typed template families, not a checker.
Captures and current dynamic input are separate. Every observed invocation checks
its decreasing rank. Well-formedness of all unvisited branches is a premise.
"""
from dataclasses import dataclass
from copy import deepcopy
from fractions import Fraction
import sys
from pathlib import Path
from occurrence_machine import Ret,Op,Bind,Batch,Case,Call,Leaf,Node,graft,leaves,ProcedureEntry
from legacy_oracle import Evaluation

@dataclass(frozen=True)
class Invoke:
    select: object  # input -> (template name, ordinary-data capture)

@dataclass(frozen=True)
class ParameterCall:
    name: str
    capture: object # already instantiated from persistent Gamma, never current input

@dataclass(frozen=True)
class Template:
    rank: int
    body: object # ordinary-data capture -> term; never receives stores/authority

class RankedAdapter:
    def __init__(self,templates,ceiling):
        self.templates=dict(templates)
        self.ceiling=ceiling
        if ceiling<0 or any(t.rank<0 or t.rank>ceiling for t in templates.values()):
            raise ValueError('invalid finite rank menu')
    def enter(self,name,capture,input_value,bound):
        t=self.templates[name]
        if t.rank>=bound: raise ValueError('nondecreasing ranked invocation')
        return t.body(deepcopy(capture)),input_value,t.rank
    def compile(self,t,bound=None):
        bound=self.ceiling+1 if bound is None else bound
        if isinstance(t,(Ret,Op)): return t
        if isinstance(t,Bind):return Bind(self.compile(t.left,bound),lambda b:self.compile(t.k(b),bound))
        if isinstance(t,Batch):return Batch(lambda a,c:tuple((self.compile(u,bound),b,cs) for u,b,cs in t.split(a,c)))
        if isinstance(t,Case):return Case(t.select,tuple(self.compile(u,bound) for u in t.terms))
        if isinstance(t,Invoke):
            def arg(a):
                name,capture=t.select(a)
                return name,capture,a,bound
            return Call('__ranked_template__',arg)
        if isinstance(t,ParameterCall):
            return Call('__ranked_template__',lambda a:(t.name,t.capture,a,bound))
        raise TypeError('outside admitted ranked finite grammar')
    def resolve(self,packed):
        body,a,rank=self.enter(*packed)
        return ProcedureEntry(self.compile(body,rank),a)
    @property
    def procedures(self):return {'__ranked_template__':self.resolve}

    def evaluate(self,t,a,caps,primitives,choose,world=None,stores=None,dimension=1,bound=None):
        """Independent source structural evaluation, not compiled-runtime execution."""
        bound=self.ceiling+1 if bound is None else bound
        world=deepcopy({} if world is None else world);stores=deepcopy(stores or {})
        def rec(u,b,cs,w=world,s=stores,limit=bound):
            return self.evaluate(u,b,cs,primitives,choose,w,s,dimension,limit)
        if isinstance(t,(Invoke,ParameterCall)):
            name,capture=t.select(a) if isinstance(t,Invoke) else (t.name,t.capture)
            body,b,rank=self.enter(name,capture,a,bound)
            return rec(body,b,caps,limit=rank)
        if isinstance(t,Ret):return Evaluation(Leaf(t.f(a),tuple(sorted(caps))),('ret',),Fraction(1),(0,)*dimension,(),world,stores)
        if isinstance(t,Op):
            alts=primitives[t.name](t.arg(a),tuple(sorted(caps)),deepcopy(world),{c:deepcopy(stores[c]) for c in caps if c in stores})
            ai,oi=choose(t.name);o=alts[ai][oi];stores.update(deepcopy(o.stores))
            return Evaluation(o.tree,('op',t.name,ai,oi,o.witness),o.weight,o.cost,(o.event,),deepcopy(o.world),stores)
        if isinstance(t,Case):return rec(t.terms[t.select(a)],a,caps)
        if isinstance(t,Bind):
            left=rec(t.left,a,caps);rs=[];world=left.world;stores=left.stores
            for b in leaves(left.tree):
                r=rec(t.k(b.value),b.value,b.caps,world,stores);rs.append(r);world=r.world;stores=r.stores
            p=left.weight
            for r in rs:p*=r.weight
            return Evaluation(graft(left.tree,[r.tree for r in rs]),('bind',left.raw,tuple(r.raw for r in rs)),p,tuple(left.cost[i]+sum(r.cost[i] for r in rs) for i in range(dimension)),left.word+tuple(e for r in rs for e in r.word),world,stores)
        if isinstance(t,Batch):
            rs=[]
            for u,b,cs in t.split(a,tuple(sorted(caps))):
                r=rec(u,b,cs,world,stores);rs.append(r);world=r.world;stores=r.stores
            p=Fraction(1)
            for r in rs:p*=r.weight
            return Evaluation(Node('Fork',tuple(r.tree for r in rs),True),('batch',tuple(r.raw for r in rs)),p,tuple(sum(r.cost[i] for r in rs) for i in range(dimension)),tuple(e for r in rs for e in r.word),world,stores)
        raise TypeError('outside admitted ranked finite grammar')


def live_store_observation(tree,stores):
    """Addressed final Store(Delta) only; retired entries are archival, not outputs."""
    def visit(t,address):
        if isinstance(t,Leaf):
            return [(address,t.value,tuple((c,deepcopy(stores[c])) for c in t.caps if c in stores))]
        return [row for i,child in enumerate(t.children) for row in visit(child,address+(i,))]
    return tuple(visit(tree,()))
