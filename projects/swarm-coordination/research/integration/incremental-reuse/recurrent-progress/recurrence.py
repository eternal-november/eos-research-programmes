"""Finite unpaid duty summaries for a fixed policy and fixed justice vocabulary."""
from dataclasses import dataclass

def adj(vertices, edges, reverse=False):
    d = {u:set() for u in vertices}
    for u,v,_ in edges:
        if reverse:
            u,v=v,u
        d[u].add(v)
    return d

def reached(start, graph):
    seen=set(start)
    todo=list(seen)
    while todo:
        for v in graph[todo.pop()] - seen:
            seen.add(v)
            todo.append(v)
    return seen

def components(graph, reverse):
    seen=set()
    order=[]
    for root in graph:
        if root in seen:
            continue
        seen.add(root)
        stack=[(root,iter(graph[root]))]
        while stack:
            u,ns=stack[-1]
            v=next(ns,None)
            if v is None:
                order.append(u)
                stack.pop()
            elif v not in seen:
                seen.add(v)
                stack.append((v,iter(graph[v])))
    seen.clear()
    for u in reversed(order):
        if u in seen:
            continue
        c=set()
        todo=[u]
        seen.add(u)
        while todo:
            v=todo.pop()
            c.add(v)
            for w in reverse[v] - seen:
                todo.append(w)
                seen.add(w)
        yield c

def groups(vertices, edges, justice):
    graph=adj(vertices,edges)
    back=adj(vertices,edges,True)
    classes=list(components(graph,back))
    index={u:i for i,c in enumerate(classes) for u in c}
    loop=[False]*len(classes)
    colors=[0]*len(classes)
    sinks=[True]*len(classes)
    for u,v,m in edges:
        i,j=index[u],index[v]
        if i==j:
            loop[i]=True
            colors[i]|=m
        else:
            sinks[i]=False
    fair={u for i,c in enumerate(classes) if loop[i] and colors[i]==justice for u in c}
    return graph,back,classes,sinks,fair

@dataclass(frozen=True)
class Module:
    vertices: frozenset
    ports: frozenset
    steps: tuple  # (origin,destination,justice subset bitmask), unpaid
    pays: frozenset  # vertices with an actual outgoing paid terminal transition

@dataclass(frozen=True)
class Summary:
    ports: frozenset
    paths: tuple
    # all five below are subsets of ports
    physical_out: frozenset
    can_pay: frozenset
    can_stop: frozenset
    can_loop: frozenset
    can_strand: frozenset
    justice: int

def summarize(module, justice):
    v,p,e,pay = module.vertices,module.ports,module.steps,module.pays
    if (not v or None in v or not p <= v or not pay <= v or justice < 0
            or any(x not in v or y not in v or m<0 or m&~justice for x,y,m in e)):
        raise ValueError('invalid sealed module')
    g,b,cs,sinks,fair=groups(v,e,justice)
    stop={u for u in v-p-pay if not g[u]}
    stranded=set().union(*(c for i,c in enumerate(cs)
                            if sinks[i] and not c & (p|pay|stop|fair)))
    fw={u:reached({u},g) for u in p}
    bw={u:reached({u},b) for u in p}
    paths=[]
    for u in p:
        for w in p:
            m=None
            for x,y,j in e:
                if x in fw[u] and y in bw[w]:
                    m=(m or 0)|j
            if m is not None:
                paths.append((u,w,m))
    def can(target):
        return frozenset(u for u in p if fw[u]&target)
    return Summary(p,tuple(paths),frozenset(u for u in p if g[u] or u in pay),
                   can(pay),can(stop),can(fair),can(stranded),justice)

def check(summaries, bridges, roots, justice):
    """Compile a new receiver view without reading unchanged module bodies."""
    if not roots or justice<0 or any(s.justice!=justice for s in summaries.values()):
        raise ValueError('unknown initial cut or changed justice')
    p={(i,u) for i,s in summaries.items() for u in s.ports}
    if not roots<=p or any(u not in p or v not in p or u[0]==v[0] or m<0 or m&~justice
                          for u,v,m in bridges):
        raise ValueError('unknown root or nonlocal edge not between verified ports')
    e=[((i,u),(i,v),m) for i,s in summaries.items() for u,v,m in s.paths] + list(bridges)
    g,b,_,_,fair=groups(p,e,justice)
    live=reached(roots,g)
    physical={u for u,_,_ in bridges}
    def marker(field):
        return {(i,u) for i,s in summaries.items() for u in getattr(s,field)}
    stop=marker('can_stop') | (p-marker('physical_out')-physical)
    loop=marker('can_loop') | fair
    pay=marker('can_pay')
    productive=reached(stop|loop|pay,b)
    stranded = bool(live-productive) or bool(live & marker('can_strand'))
    return dict(finite_unpaid=bool(live&stop),fair_unpaid=bool(live&loop),
                paid_terminal=bool(live&pay),stranded_prefix=stranded)
