"""Exact finite proof replay under a complete, explicitly delivered change."""
from collections import deque
from dataclasses import dataclass, field
from typing import NamedTuple

class Observation(NamedTuple):
    # An entire information class: actor, deadline cut and observable history.
    actor: str
    cut: str
    history: str
    action: str

@dataclass(frozen=True)
class Fact:
    bad: frozenset[str] = frozenset()
    obs: Observation | None = None

@dataclass
class Graph:
    roots: frozenset[str]
    out: dict[str, frozenset[str]]
    facts: dict[str, Fact]
    rev: dict[str, frozenset[str]] = field(init=False)
    def __post_init__(self):
        states=set(self.out)
        assert self.roots<=states and states==set(self.facts)
        back={v:set() for v in states}
        for p,succ in self.out.items():
            for v in succ:
                back[v].add(p)
        self.rev={v:frozenset(z) for v,z in back.items()}

@dataclass(frozen=True)
class Edits:
    roots: frozenset[str] | None = None
    out: dict[str, frozenset[str]] = field(default_factory=dict)
    facts: dict[str, Fact] = field(default_factory=dict)

@dataclass
class Cache:
    parent: dict[str,str|None]
    bad: dict[str, set[str]]
    views: dict[tuple[str,str,str], dict[str,set[str]]]
    conflicts: set[tuple[str,str,str]]

def new_graph(g:Graph, e:Edits):
    # This prototype constructs complete maps; its read counts below are
    # checking work and not measured cost of copying/indexing those maps.
    assert e.out.keys()<=g.out.keys() and e.facts.keys()<=g.facts.keys()
    return Graph(g.roots if e.roots is None else e.roots, g.out|e.out, g.facts|e.facts)

def bfs(seeds, out, allowed=None):
    parent=dict(seeds)
    active=deque(sorted(parent))
    reads=0
    while active:
        u=active.popleft()
        succ=out[u]
        reads+=1
        for v in sorted(succ):
            if (allowed is None or v in allowed) and v not in parent:
                parent[v]=u
                active.append(v)
    return parent,reads

def change_fact(c,k,f,add):
    for label in f.bad:
        bucket=c.bad.setdefault(label,set())
        (bucket.add if add else bucket.discard)(k)
    if f.obs is None:
        return
    key=f.obs[:3]
    kinds=c.views.setdefault(key,{})
    bucket=kinds.setdefault(f.obs.action,set())
    if add:
        bucket.add(k)
    else:
        bucket.remove(k)
        if not bucket:
            del kinds[f.obs.action]
    if len(kinds)>1:
        c.conflicts.add(key)
    else:
        c.conflicts.discard(key)

def full(g):
    root={k:None for k in g.roots}
    reach, reads=bfs(root,g.out)
    result=Cache(reach,{}, {},set())
    for k in reach:
        change_fact(result,k,g.facts[k],True)
    return result, dict(out_reads=reads,fact_reads=len(reach))

def update(g:Graph, c:Cache, e:Edits):
    """Patch dirty cone, recompute only new entrance-support witnesses.

    c is the previously validated cache for g. Changes are supplied as edits,
    not as a lossy list of 'suspect modules.' No mutated state may escape e.
    """
    new=new_graph(g,e)
    added_roots=new.roots-g.roots
    cone=set(g.roots^new.roots)
    for u,after in e.out.items():
        cone.update(g.out[u]^after)
    todo=deque(cone)
    while todo:
        u=todo.popleft()
        for v in g.out[u]|new.out[u]:
            if v not in cone:
                cone.add(v);todo.append(v)

    seeds={k:None for k in (new.roots&cone)}
    for v in sorted(cone-seeds.keys()):
        # The old reached certificate outside the cone is still sound.
        inbounds=sorted(u for u in new.rev[v] if u not in cone and u in c.parent)
        if inbounds:
            seeds[v]=inbounds[0]
    new_inside,reads=bfs(seeds,new.out,cone)
    parent={v:u for v,u in c.parent.items() if v not in cone}
    parent.update(new_inside)
    # Only changed reachable membership or changed fact can affect verdict.
    remove=(c.parent.keys()-parent.keys()) | (e.facts.keys() & c.parent.keys())
    add=(parent.keys()-c.parent.keys()) | (e.facts.keys() & parent.keys())
    import copy
    patched=Cache(parent,copy.deepcopy(c.bad),copy.deepcopy(c.views),set(c.conflicts))
    for k in remove:change_fact(patched,k,g.facts[k],False)
    for k in add:change_fact(patched,k,new.facts[k],True)
    m=dict(out_reads=len(e.out)+2*len(cone)+reads,reverse_reads=len(cone),
           fact_reads=len(remove)+len(add),cone_size=len(cone),
           retained=len(parent)-len(new_inside),repaired=len(new_inside))
    return new,patched,m

def path(c,key):
    result=[]
    while key is not None:
        assert key not in result,"a cyclic predecessor is not evidence"
        result.append(key)
        key=c.parent[key]
    return list(reversed(result))

def validate_path(g,p):
    return bool(p) and p[0] in g.roots and all(y in g.out[x] for x,y in zip(p,p[1:]))

def witnesses(c,labels):
    out={}
    for v in labels:
        ys=c.bad.get(v)
        out[v]=path(c,min(ys)) if ys else None
    if c.conflicts:
        k=min(c.conflicts)
        alternatives=c.views[k]
        a,b=sorted(alternatives)[:2]
        out["realizability"]=(path(c,min(alternatives[a])),path(c,min(alternatives[b])))
    else:
        out["realizability"]=None
    return out

def infer(rows):
    """Rows are explicit mutually exclusive installation completions.

    'refuted' on all possible installations may need a witness family;
    no single counterhistory is asserted to be observed when evidence
    has not selected a unique installed graph.
    """
    assert rows
    if all(w is None for w in rows.values()):
        return "carries"
    if all(w is not None for w in rows.values()):
        return "refuted"
    return "undecided"
