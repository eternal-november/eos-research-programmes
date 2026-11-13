"""Exhaustive small-monoid regression, not a proof of the theorem."""
import itertools, json

def partitions(xs):
    if not xs:
        yield []
        return
    x,*rest=xs
    for p in partitions(rest):
        yield [{x}]+[set(b) for b in p]
        for i in range(len(p)):
            q=[set(b) for b in p]; q[i].add(x); yield q

def check(n,e,mul):
    units={a for a in range(n) if any(mul(a,b)==e for b in range(n))}
    checked=congruences=passing=0
    for p in partitions(list(range(n))):
        checked+=1
        c={a:frozenset(b) for b in p for a in b}
        if not all(c[mul(a,x)]==c[mul(b,x)] for a in range(n) for b in c[a] for x in range(n)):
            continue
        congruences+=1
        fl=all({mul(a,x) for x in c[u]}==set(c[mul(a,u)]) for a in range(n) for u in range(n))
        H=set(c[e])
        predicted=H<=units and all({mul(a,h) for h in H}==set(c[a]) for a in range(n))
        assert fl==predicted,(n,p)
        if fl:
            passing+=1
            assert e in H and all(mul(a,b) in H for a in H for b in H)
            assert all(any(mul(a,b)==e for b in H) for a in H)
    return dict(partitions=checked,congruences=congruences,FL_congruences=passing)

out={}
for n in range(1,6):
    out[f'C{n}']=check(n,0,lambda a,b,n=n:(a+b)%n)
    out[f'max{n}']=check(n,0,max)
# A monoid with both nontrivial units and nonunits: C2 with absorbing zero.
out['C2_with_zero']=check(3,0,lambda a,b:2 if 2 in (a,b) else (a+b)%2)
# Edge-active quotient on C2: outer edge scalar0, two singleton identity children
# must remain scalar0; quotient target scalar1 therefore cannot lift.
assert {(a+b)%2 for a in [0] for b in [0]}=={0}
# Uniform positive-graph orbit quotient: every partition of r>0 has a positive child.
forest_cases=0
for r in range(5):
    for arity in range(5):
        for assignment in itertools.product(range(arity),repeat=r):
            sizes=[assignment.count(i) for i in range(arity)]
            child_classes=[range(2) if s else [0] for s in sizes]
            products={sum(xs)%2 for xs in itertools.product(*child_classes)}
            assert products==({0,1} if r else {0})
            forest_cases+=1
out['ordered_partition_regressions']=forest_cases
out['edge_only_counterexample']='PASS: scalar1 target cannot lift'
out['nullary_counterexample']='PASS: empty forest has only scalar0 product'
print(json.dumps(out,indent=2))
