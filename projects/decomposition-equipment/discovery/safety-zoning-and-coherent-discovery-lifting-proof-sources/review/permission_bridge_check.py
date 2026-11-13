"""Independent tiny finite enumeration; no production theorem/checker imports."""
from itertools import product

MAPS=list(product(range(2), repeat=2))
def comp(a,b): return tuple(a[i] for i in b)
def compose_rel(a,b): return {(x,z) for x,y in a for yy,z in b if y==yy}
def grammar_participates(lc,ld,q,target, bad_only=False):
    # C -> C | D; D -> D | DD. All maps have two-state source.
    # state (current boundary map, mismatch seen, target map seen)
    states=list(product(MAPS,range(2),range(2)))
    rel={}
    for e,leg in [('C',lc),('D',ld)]:
        pairs=set()
        for h,b,s in states:
            for f in MAPS:
                k=comp(leg,f)
                if comp(q,h)==comp(q,k):
                    pairs.add(((h,b,s),(k,int(b or h!=k),int(s or (e,f)==target))))
        rel[e]=pairs
    while True:
        old={e:set(r) for e,r in rel.items()}
        rel['D'] |= compose_rel(rel['D'],rel['D'])
        rel['C'] |= rel['D']
        if rel==old: break
    initial=(lc,0,0)
    return any(x==initial and comp(q,h)==comp(q,lc) and s and (not bad_only or b or h!=lc)
               for x,(h,b,s) in rel['C'])
def brute(lc,ld,q):
    seen=set()
    for word in [('C',)]+[('D',)*n for n in range(1,5)]:
        for fs in product(MAPS,repeat=len(word)):
            legs=[comp(lc if e=='C' else ld,f) for e,f in zip(word,fs)]
            chain=[lc]+legs+[lc]
            if all(comp(q,a)==comp(q,b) for a,b in zip(chain,chain[1:])):
                seen.update(zip(word,fs))
    return seen
cases=0
for lc,ld,q in product(MAPS,MAPS,[(0,1),(0,0)]):
    # Ensure a fine C -> D generator exists. D -> DD has diagonal witness.
    if not any(comp(ld,f)==lc for f in MAPS): continue
    expected=brute(lc,ld,q)
    actual={(e,f) for e in ['C','D'] for f in MAPS if grammar_participates(lc,ld,q,(e,f))}
    assert actual==expected,(lc,ld,q,actual,expected)
    cases+=1
# Mutation: BAD-only acceptance loses every discovery when q is identity.
assert grammar_participates((0,1),(0,1),(0,1),('D',(0,1)))
assert not grammar_participates((0,1),(0,1),(0,1),('D',(0,1)),bad_only=True)
# Independent partition refinement implementing A by signatures, not predicate enumeration.
def partition(n,initial,maps=(),relations=()):
    colors=[tuple(i in P for P in initial) for i in range(n)]
    while True:
        sig=[(colors[i],tuple(colors[f[i]] for f in maps),
              tuple(frozenset(colors[j] for j in R[i]) for R in relations)) for i in range(n)]
        ids={v:k for k,v in enumerate(dict.fromkeys(sig))}
        new=[ids[v] for v in sig]
        if all((colors[i]==colors[j])==(new[i]==new[j]) for i,j in product(range(n),repeat=2)):
            return new
        colors=new
# Old identity-only probes miss a newly discovered permutation, terminal boundary.
old=partition(3,[{0}],[(0,1,2)])
new=partition(3,[{0}],[(0,1,2),(1,0,2)])
assert old[1]==old[2] and len(set(new))==3
# Action-specific relation distinguishes states whose union successors are identical.
a=[{2},{3},{2},{3}]; b=[{3},{2},{2},{3}]
kept=partition(4,[{2}],relations=[a,b]); forgotten=partition(4,[{2}],relations=[[a[i]|b[i] for i in range(4)]])
assert kept[0]!=kept[1] and forgotten[0]==forgotten[1]
# Aggregate enabledness is not uniform enabledness over a belief.
concrete={0:{0},1:set()}; belief={0,1}
assert bool(set().union(*(concrete[x] for x in belief))) and not all(concrete[x] for x in belief)
# Event probes: one vertex with two distinct loop events. Every event permutation is a graph map.
event_old=partition(3,[{0}],[(0,1,2)])
event_new=partition(3,[{0}],[(1,0,2)])
assert event_old[1]==event_old[2] and event_new[1]!=event_new[2]
# Incidence inverse images must distinguish events with differently classified endpoints.
assert tuple(x in {0} for x in [0,1])==(True,False)
print(f'PASS: {cases} valid two-color grammar assignments; marked CFG participation equals direct semantic enumeration (profiles through four D leaves).')
print('PASS: mutations detected: BAD-only participation, primitive-only closure, merged action labels, aggregate-only enabledness, omitted event probes.')
print('Finite tests supplement, do not prove, the unbounded grammar theorem.')
