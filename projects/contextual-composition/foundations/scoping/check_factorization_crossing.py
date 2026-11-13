"""Exact finite test of a proposed partial-to-quotient crossing. No theorem assumed."""
from dataclasses import dataclass
@dataclass
class Mixed:
    source: frozenset
    target: frozenset
    domain: frozenset
    outputs: frozenset
    run: dict
    quotient: dict
    def validate(self):
        assert self.domain <= self.source
        assert set(self.run)==set(self.domain)
        assert set(self.run.values()) <= self.outputs
        assert set(self.quotient)==set(self.target)
        assert set(self.quotient.values()) == set(self.outputs)
        return self

def then(m,n):
    m.validate();n.validate();assert m.target==n.source
    # Image factorization of n.domain -> m.target -> m.outputs.
    w=frozenset(m.quotient[u] for u in n.domain)
    domain=frozenset(x for x in m.domain if m.run[x] in w)
    # Pushout of n.domain -> w and n.domain -> n.outputs.
    nodes={('w',x) for x in w}|{('v',x) for x in n.outputs}
    parent={x:x for x in nodes}
    def find(x):
        while parent[x]!=x:
            parent[x]=parent[parent[x]];x=parent[x]
        return x
    def union(x,y):
        a,b=find(x),find(y)
        if a!=b: parent[a]=b
    for u in n.domain: union(('w',m.quotient[u]),('v',n.run[u]))
    blocks={x:frozenset(y for y in nodes if find(y)==find(x)) for x in nodes}
    return Mixed(m.source,n.target,domain,frozenset(blocks.values()),
                 {x:blocks[('w',m.run[x])] for x in domain},
                 {c:blocks[('v',n.quotient[c])] for c in n.target}).validate()

A=frozenset(['a0','a1']);B=frozenset(['b0','b1','b2','b3'])
C=frozenset(['c0','c1','c2']);D=frozenset(['*'])
f=Mixed(A,B,A,frozenset(['q0','q1']),{'a0':'q0','a1':'q1'},
        {'b0':'q0','b1':'q0','b2':'q1','b3':'q1'}).validate()
g=Mixed(B,C,B,C,{'b0':'c0','b1':'c1','b2':'c1','b3':'c2'}, {x:x for x in C}).validate()
h=Mixed(C,D,frozenset(['c2']),D,{'c2':'*'},{'*':'*'}).validate()
left=then(then(f,g),h); right=then(f,then(g,h))
assert left.domain==A
assert right.domain==frozenset(['a1'])
assert left.domain!=right.domain
print('((f then g) then h) domain:',sorted(left.domain))
print('(f then (g then h)) domain:',sorted(right.domain))
print('Associativity fails for this image-factorization + pullback/pushout recipe.')
