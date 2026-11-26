"""Finite construction from a declared many-sorted primitive interface."""

from itertools import product


def audit(domains,targets,maps,primitives):
    """Entry: (factor name, component indices, source evaluator, target evaluator)."""
    sigs=[[[] for _ in ts] for ts in targets]
    reflection=[]
    for name,scope,source,target in primitives:
        for xs in product(*(domains[i] for i in scope)):
            ys=tuple(maps[i][x] for i,x in zip(scope,xs,strict=True))
            own,other=source(*xs),target(*ys)
            if own!=other:
                reflection.append((name,xs,own,other))
        for slot,i in enumerate(scope):
            surroundings=[targets[j] if k!=slot else (None,) for k,j in enumerate(scope)]
            for u,x in enumerate(targets[i]):
                for context in product(*surroundings):
                    args=(*context[:slot],x,*context[slot+1:])
                    sigs[i][u].append(target(*args))
    q=[]
    for carrier,signature in zip(targets,sigs,strict=True):
        signatures={}
        table={}
        for x,s in zip(carrier,signature,strict=True):
            table[x]=signatures.setdefault(tuple(s),len(signatures))
        q.append(table)
    missing=tuple(tuple(sorted(set(t.values())-{t[f[x]] for x in d}))
                  for t,f,d in zip(q,maps,domains,strict=True))
    return q,reflection,missing


def assembled_profile(q,primitives):
    tables={}
    for name,scope,_,target in primitives:
        local={}
        for x in product(*(q[i] for i in scope)):
            sig=tuple(q[i][j] for i,j in zip(scope,x,strict=True))
            got=target(*x)
            assert sig not in local or local[sig]==got
            local[sig]=got
        tables[name]=local
    return tables
