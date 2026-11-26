import json
import random
from itertools import product, combinations
from collections import Counter
from recurrence import Module, summarize, adj, reached, components
from streett import Source, compile, verify

def flatten(bodies, bridges):
    ns={(i,u) for i,s in bodies.items() for u in s.vertices}
    es=[((i,u),(i,v),e,t) for i,s in bodies.items() for u,v,e,t in s.steps]+list(bridges)
    pay={(i,u) for i,s in bodies.items() for u in s.pays}
    return ns,es,pay

def direct_cores(nodes, edges):
    """Exact whole-graph Streett SCC pruning; no suffix-choice enumeration."""
    todo=[(nodes,edges)]
    good=set()
    while todo:
        ns,es=todo.pop()
        thin=[(u,v,0) for u,v,_,_ in es]
        for c in components(adj(ns,thin),adj(ns,thin,True)):
            inside=[row for row in es if row[0] in c and row[1] in c]
            if not inside:
                continue
            en=take=0
            for _,_,e,t in inside:
                en|=e; take|=t
            bad=en & ~take
            if not bad:
                good |= c
            else:
                todo.append((c,[row for row in inside if not row[2]&bad]))
    return good

def brute_cores(nodes, edges):
    # Enumerate every nonempty possible infinitely recurrent edge support.
    ans=set()
    for mask in range(1,1<<len(edges)):
        es=[row for i,row in enumerate(edges) if (mask>>i)&1]
        verts={a for u,v,_,_ in es for a in (u,v)}
        graph={u:set() for u in verts}
        back={u:set() for u in verts}
        en=take=0
        for u,v,e,t in es:
            en|=e; take|=t
            graph[u].add(v); back[v].add(u)
        at=next(iter(verts))
        def closure(g):
            s={at}
            for _ in verts:
                s|={x for u in s for x in g[u]}
            return s
        if not en&~take and closure(graph)==verts and closure(back)==verts:
            ans|=verts
    return ans

def direct(bodies,bridges,roots,oracle):
    ns,es,pay=flatten(bodies,bridges)
    thin=[(u,v,0) for u,v,_,_ in es]
    g,b=adj(ns,thin),adj(ns,thin,True)
    fair=oracle(ns,es)
    stop={u for u in ns-pay if not g[u]}
    live=reached(roots,g)
    return dict(finite_unpaid=bool(live&stop),fair_unpaid=bool(live&fair),
                paid_terminal=bool(live&pay),stranded_prefix=bool(live-reached(stop|fair|pay,b)))

def run(bodies,bridges,roots,k,brute=True):
    s={i:compile(part,k) for i,part in bodies.items()}
    ans=verify(s,bridges,roots,k)
    assert ans==direct(bodies,bridges,roots,direct_cores)
    if brute:
        assert ans==direct(bodies,bridges,roots,brute_cores)
    return ans

def make(ns,ports,steps,pays):
    return Source(frozenset(ns),frozenset(ports),tuple(steps),frozenset(pays))

def weak(part,k):
    m=(1<<k)-1
    return summarize(Module(part.vertices,part.ports,
        tuple((u,v,(m&~e)|t) for u,v,e,t in part.steps),part.pays),m)

# The full enable branch ensures old weak and positive union summaries agree.
# Every finite prefix admits payment, independent of which tour is selected.
profiles=0
classes={}
for k in range(2,5):
    m=(1<<k)-1
    d=k//2
    middle=[sum(1<<i for i in A) for A in combinations(range(k),d)]
    words=set()
    old=None
    for word in range(1<<len(middle)):
        masked=[A for i,A in enumerate(middle) if (word>>i)&1]
        branches=[m]+masked
        interior=range(2,len(branches)+2)
        e=[row for n,A in zip(interior,branches)
           for row in [(0,n,0,0),(n,1,A,0)]]
        local=make(range(len(branches)+2),[0,1],e,range(len(branches)+2))
        same=weak(local,k)
        if old is None:
            old=same
        assert same==old
        remote=make([0],[0],[],[0])
        bodies={0:local,1:remote}
        summary={i:compile(s,k) for i,s in bodies.items()}
        out=0
        for i,K in enumerate(middle):
            bridges=[((0,1),(1,0),0,0),((1,0),(0,0),K,K)]
            z=verify(summary,bridges,{(0,0)},k)
            assert z==direct(bodies,bridges,{(0,0)},direct_cores)
            assert z==dict(finite_unpaid=False,fair_unpaid=bool((word>>i)&1),
                           paid_terminal=True,stranded_prefix=False)
            out|=int(z['fair_unpaid'])<<i
            profiles+=1
        words.add(out)
    assert len(words)==1<<len(middle)
    classes[k]=dict(interface_bits=len(middle),behavior_classes=len(words))

# A forbidden opportunity in the prefix must not prevent an eventual
# suffix; because payment is outside the suffix, it is not a deadlock.
prefix=make(range(2),[0],[(0,1,1,0),(1,1,0,0)],[1])
assert run({0:prefix},[],{(0,0)},1)==dict(
    finite_unpaid=False,fair_unpaid=True,paid_terminal=True,stranded_prefix=False)
# A sealed unfair inner trap keeps the initial model from passing vacuously.
trap=make(range(2),[0],[(0,1,1,0),(1,1,1,0)],[0])
assert run({0:trap},[],{(0,0)},1)==dict(
    finite_unpaid=False,fair_unpaid=False,paid_terminal=True,stranded_prefix=True)
# The full-state opportunity drives the verdict even if the only T exits
# at that vertex are outside the unpaid subgraph.
with_exit=make([0],[0],[(0,0,1,0)],[0])
assert not run({0:with_exit},[],{(0,0)},1)['fair_unpaid']

randomized=0
rng=random.Random(1997)
for _ in range(3500):
    k=rng.randrange(4)
    m=(1<<k)-1
    bodies={}
    for i in range(rng.randint(1,3)):
        n=rng.randint(1,3)
        p=rng.sample(range(n),rng.randint(1,n))
        s=rng.sample(list(product(range(n),repeat=2)),rng.randrange(3 if n>1 else 2))
        steps=[]
        for u,v in s:
            e=rng.randint(0,m)
            steps.append((u,v,e,rng.randint(0,m)&e))
        bodies[i]=make(range(n),p,steps,[u for u in range(n) if rng.random()<.32])
    ports=[(i,u) for i,s in bodies.items() for u in sorted(s.ports)]
    pairs=[(u,v) for u,v in product(ports,repeat=2) if u[0]!=v[0]]
    eb=[]
    for u,v in rng.sample(pairs,min(len(pairs),rng.randrange(3))):
        e=rng.randint(0,m)
        eb.append((u,v,e,rng.randint(0,m)&e))
    # Half the cases stamp a common original enablement mask at each
    # origin vertex; the other half exercise general transition annotations.
    if randomized%2==0:
        labels={(i,u):rng.randint(0,m) for i,b in bodies.items() for u in b.vertices}
        bodies={i:make(b.vertices,b.ports,
            [(u,v,labels[i,u],t&labels[i,u]) for u,v,_,t in b.steps],b.pays)
            for i,b in bodies.items()}
        eb=[(u,v,labels[u],t&labels[u]) for u,v,_,t in eb]
    roots=set(rng.sample(ports,rng.randint(1,min(3,len(ports)))))
    run(bodies,eb,roots,k)
    randomized+=1

print(json.dumps(dict(finite_controls=3,randomized_graphs=randomized,
           middle_layer_comparisons=profiles, distinguishable_summary_classes=classes),
           sort_keys=True))
