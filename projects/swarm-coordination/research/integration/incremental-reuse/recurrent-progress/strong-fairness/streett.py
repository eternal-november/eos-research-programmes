"""Reusable strongly fair recurrence for a fixed installed finite graph."""
from dataclasses import dataclass
from recurrence import Module, adj, reached, groups, summarize

@dataclass(frozen=True)
class Source:
    vertices: frozenset
    ports: frozenset
    steps: tuple # (origin, destination, original enable mask, actual occurrence mask)
    pays: frozenset  # actual OUTGOING terminal payment at that vertex

@dataclass(frozen=True)
class Seal:
    base: object
    suffixes: tuple # per forbidden mask, nonempty arcs labelled by remaining occurrences
    internal: frozenset
    stranded: frozenset
    k: int

def valid_masks(e,t,k):
    return 0<=t and 0<=e<(1<<k) and (t & ~e)==0

def compile(source,k):
    v,p,s,pay=source.vertices,source.ports,source.steps,source.pays
    if k<0 or any(not valid_masks(e,t,k) for x,y,e,t in s):
        raise ValueError('bad original opportunity/occurrence vocabulary')
    raw=tuple((u,v,0) for u,v,_,_ in s)
    base=summarize(Module(v,p,raw,pay),0)
    g,_,cs,sinks,_=groups(v,raw,0)
    f=set()
    charts=[]
    for j in range(1<<k):
        need=((1<<k)-1)^j
        filtered=tuple((u,v,t&need) for u,v,e,t in s if not e&j)
        m=summarize(Module(v,p,filtered,pay),need)
        charts.append(m.paths)
        f|=groups(v,filtered,need)[-1]
    stop={u for u in v-p-pay if not g[u]}
    traps=set().union(*(c for i,c in enumerate(cs) if sinks[i] and not c&(p|pay|stop|f)))
    visits={u:reached({u},g) for u in p}
    return Seal(base,tuple(charts),frozenset(u for u in p if visits[u]&f),
                frozenset(u for u in p if visits[u]&traps),k)

def verify(seals,bridges,roots,k):
    if k<0 or not roots or any(s.k!=k for s in seals.values()):
        raise ValueError('incompatible or empty cut')
    ps={(u,p) for u,s in seals.items() for p in s.base.ports}
    if not roots<=ps or any(u not in ps or v not in ps or u[0]==v[0]
                              or not valid_masks(e,t,k) for u,v,e,t in bridges):
        raise ValueError('unknown root or bridge boundary')
    base=[((i,u),(i,v),0) for i,s in seals.items() for u,v,_ in s.base.paths]
    base.extend((u,v,0) for u,v,_,_ in bridges)
    g,b=adj(ps,base),adj(ps,base,True)
    live=reached(roots,g)
    def field(name):
        return {(i,u) for i,s in seals.items() for u in getattr(s.base,name)}
    physical={u for u,_,_,_ in bridges}
    pay=field('can_pay')
    stop=field('can_stop')|(ps-field('physical_out')-physical)
    fair={(i,u) for i,s in seals.items() for u in s.internal}
    for j in range(1<<k):
        need=((1<<k)-1)^j
        inside=[((i,u),(i,v),m) for i,s in seals.items() for u,v,m in s.suffixes[j]]
        inside.extend((u,v,t&need) for u,v,e,t in bridges if not e&j)
        fair|=groups(ps,inside,need)[-1]
    # Original reachability is used for every finite prefix.
    stranded_in={(i,u) for i,s in seals.items() for u in s.stranded}
    return dict(finite_unpaid=bool(live&stop),fair_unpaid=bool(live&fair),
                paid_terminal=bool(live&pay),
                stranded_prefix=bool(live-reached(stop|fair|pay,b) or live&stranded_in))
