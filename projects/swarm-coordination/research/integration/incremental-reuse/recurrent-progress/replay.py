import json
import random
from collections import Counter
from itertools import product
from recurrence import Module, check, summarize, groups, reached

def flatten(bodies,bridges):
    ns={(i,u) for i,a in bodies.items() for u in a.vertices}
    es=[((i,u),(i,v),m) for i,a in bodies.items() for u,v,m in a.steps]+list(bridges)
    pays={(i,u) for i,a in bodies.items() for u in a.pays}
    return ns,es,pays

def direct(bodies,bridges,roots,justice):
    """Strong exact factored-direct check when given the whole actual graph."""
    ns,es,pays=flatten(bodies,bridges)
    g,b,_,_,loops=groups(ns,es,justice)
    live=reached(roots,g)
    stops={u for u in ns-pays if not g[u]}
    return dict(finite_unpaid=bool(live&stops),fair_unpaid=bool(live&loops),
                paid_terminal=bool(live&pays),
                stranded_prefix=bool(live-reached(stops|loops|pays,b)))

def closure_oracle(bodies,bridges,roots,justice):
    """Explicit product of vertex and visited colors, no SCC or summaries."""
    nodes,steps,pays=flatten(bodies,bridges)
    out={x:[] for x in nodes}
    for x,y,j in steps:
        out[x].append((y,j))
    def search(init, neighbors):
        ans,todo = set(init),list(init)
        while todo:
            t=todo.pop()
            for w in neighbors(t):
                if w not in ans:
                    ans.add(w)
                    todo.append(w)
        return ans
    def reach1(x):
        return search({x}, lambda u: [v for v,_ in out[u]])
    live=search(roots, lambda u: [v for v,_ in out[u]])
    stops={x for x in nodes-pays if not out[x]}
    fair={x for x in live if (x,justice) in search(
        out[x],lambda h:[(y,h[1]|m) for y,m in out[h[0]]])}
    return dict(finite_unpaid=bool(live&stops),fair_unpaid=bool(fair),
                paid_terminal=bool(live&pays),
                stranded_prefix=any(not reach1(x)&(stops|fair|pays) for x in live))

def M(n, p, e, s=()):
    return Module(frozenset(range(n)),frozenset(p),tuple(e),frozenset(s))

def run(bodies, bridges, roots, j, slow=True):
    summaries={i:summarize(a,j) for i,a in bodies.items()}
    z=check(summaries,bridges,roots,j)
    assert z==direct(bodies,bridges,roots,j)
    if slow:
        assert z==closure_oracle(bodies,bridges,roots,j)
    return z

roots={(0,0)}
# Two interchangeable outcomes at the same port. Two colors recur only after
# a fact refinements check turns a previously colorless retry into a poll.
a=M(2,[0],[(0,1,2)],[0,1])
b=M(1,[0],[],[0])
before=[((0,0),(1,0),1),((1,0),(0,0),0)]
after =[((0,0),(1,0),1),((1,0),(0,0),2)]
q0,q1=(run({0:a,1:b},e,roots,3) for e in [before,after])
assert q0==dict(finite_unpaid=False,fair_unpaid=False,paid_terminal=True,stranded_prefix=False)
assert q1==q0|dict(fair_unpaid=True)
# In both versions the same two colors occur somewhere reachable: color 2
# is already present on the transient branch before it is added to the loop.
from functools import reduce
def visible_support(bridges):
    ns,es,_=flatten({0:a,1:b},bridges)
    g,_,_,_,_=groups(ns,es,3)
    vs=reached(roots,g)
    return vs,reduce(int.__or__,(m for u,v,m in es if u in vs),0)
assert visible_support(before)==visible_support(after)

# A reachable interior terminal cycle has no port. It is not a counterexample
# under the stipulated justice, but rejecting it cannot yield acceptance.
trap=M(2,[0],[(0,1,1),(1,1,1)],[0])
q2=run({0:trap},[],roots,3)
assert q2==q0|dict(stranded_prefix=True)
# One external bridge no longer exits: boundary dead end is a finite legal stop,
# not an unfair infinite wait. A paid outgoing action suppresses that dead end.
assert run({0:M(1,[0],[])},[],roots,3)==q0|dict(finite_unpaid=True,paid_terminal=False)
assert not run({0:a},[],roots,3)['finite_unpaid']
# A return summary unions two individually insufficient paths. Repeated module
# excursions can take both, but a prefix through the same paths is not fair.
c=M(4,[0,1],[(0,2,1),(2,1,0),(0,3,2),(3,1,0)],[1])
c2=M(1,[0],[],[0])
leave=((0,1),(1,0),0)
ret=((1,0),(0,0),0)
assert run({0:c,1:c2},[leave,ret],roots,3)['fair_unpaid']
assert not run({0:c,1:c2},[leave],roots,3)['fair_unpaid']

# Exhaust all two-singleton graphs with one optional color set for each
# self-loop/bridge; -1 is absent, 0 is present but has no color.
exhaustive=0
for a0,a1,b0,b1 in product(range(-1,4),repeat=4):
    for p0,p1 in product((False,True),repeat=2):
        for j in (0,1,3):
            arm=lambda x,p:M(1,[0],[(0,0,x&j)] if x>=0 else [],[0] if p else [])
            bs=[((i,0),(1-i,0),v&j) for i,v in enumerate((b0,b1)) if v>=0]
            run({0:arm(a0,p0),1:arm(a1,p1)},bs,roots,j)
            exhaustive+=1

rng=random.Random(371417)
counts=Counter()
for _ in range(3000):
    j=rng.choice([0,1,3,7])
    bodies={}
    for i in range(rng.randrange(1,5)):
        n=rng.randrange(1,6)
        p=rng.sample(range(n),rng.randrange(1,n+1))
        e=[(u,v,rng.randint(0,j)) for u,v in product(range(n),repeat=2)
           if rng.random()<.24]
        s=[u for u in range(n) if rng.random()<.21]
        bodies[i]=M(n,p,e,s)
    ports=[(i,u) for i,m in bodies.items() for u in sorted(m.ports)]
    bs=[(u,v,rng.randint(0,j)) for u,v in product(ports,repeat=2)
        if u[0]!=v[0] and rng.random()<.09]
    rs=set(rng.sample(ports,rng.randint(1,min(len(ports),3))))
    z=run(bodies,bs,rs,j)
    counts[tuple(k for k,v in z.items() if v)]+=1

# Work accounting: source modules (with 30-step physical corridors) on an
# acyclic chain. Only the last module body changes. Compiled direct sharing
# the same separators is intentionally the same checked mechanism.
n=32
width=31
def corridor(last=False):
    e=[(u,u+1,0) for u in range(width-1)]
    if last:
        e.append((width-1,width-1,3))
    return M(width,[0,width-1],e,[width-1])
bodies={i:corridor() for i in range(n)}
bridges=[((i,width-1),(i+1,0),0) for i in range(n-1)]
ss={i:summarize(m,3) for i,m in bodies.items()}
assert not check(ss,bridges,roots,3)['fair_unpaid']
bodies[n-1]=corridor(last=True)
ss[n-1]=summarize(bodies[n-1],3)
warm=check(ss,bridges,roots,3)
assert warm==direct(bodies,bridges,roots,3) and warm['fair_unpaid']
assert check(dict(ss),bridges,roots,3)==warm
print(json.dumps(dict(exhaustive=exhaustive,randomized_count=sum(counts.values()),
    randomized_outcomes={','.join(k):v for k,v in counts.items()},
    bridge_edit={'before':q0,'after':q1,'stranded_prefix':q2,
                 'explicit_lasso':[[0,0],[1,0],[0,0]],'justice':[1,2]},
    structural_work=dict(one_changed_module_edge_rows=len(bodies[n-1].steps),
        all_internal_edge_rows=sum(len(m.steps) for m in bodies.values()),
        quotient_vertices=sum(len(m.ports) for m in bodies.values()),
        quotient_edges=len(bridges)+sum(len(s.paths) for s in ss.values()))),
    sort_keys=True))
