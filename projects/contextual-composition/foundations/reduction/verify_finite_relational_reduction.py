"""Exact finite checks for presentation normalization versus relational composition.
Standard library only. All checks use explicit failures, so -O has the same effect.
"""
from dataclasses import dataclass
from itertools import product, combinations


def check(p, message):
    if not p: raise AssertionError(message)

@dataclass(frozen=True)
class Mixed:
    source: frozenset
    target: frozenset
    domain: frozenset
    blocks: frozenset
    run: tuple
    def fmap(self): return dict(self.run)
    def qmap(self): return {b: q for q in self.blocks for b in q}
    def validate(self):
        check(self.domain <= self.source, 'domain')
        check(set(self.fmap()) == set(self.domain), 'run domain')
        check(set(self.fmap().values()) <= self.blocks, 'run range')
        check(all(self.blocks), 'empty quotient block')
        check(sum(map(len,self.blocks)) == len(self.target), 'partition count')
        check(set().union(*self.blocks) == set(self.target) if self.blocks else not self.target, 'partition union')
        return self


def relation(m):
    f=m.fmap()
    return frozenset((a,b) for a in m.domain for b in f[a])


def compose_rel(r,s):
    return frozenset((a,c) for a,b in r for b2,c in s if b==b2)


def components(nodes,edges):
    parent={x:x for x in nodes}
    def find(x):
        while parent[x] != x:
            parent[x]=parent[parent[x]]; x=parent[x]
        return x
    for x,y in edges:
        px,py=find(x),find(y)
        if px!=py: parent[px]=py
    return {x: frozenset(y for y in nodes if find(x)==find(y)) for x in nodes}


def dfclosure(r):
    nodes={('a',a) for a,b in r}|{('b',b) for a,b in r}
    cs=components(nodes,[(('a',a),('b',b)) for a,b in r])
    return frozenset((a,b) for side,a in nodes if side=='a'
                     for side2,b in cs[(side,a)] if side2=='b')


def difunctional(r):
    return all((a,d) in r for a,b in r for c,b2 in r for c2,d in r if b==b2 and c==c2)


def then(m,n):
    m.validate(); n.validate(); check(m.target==n.source, 'middle object')
    q=m.qmap(); f=m.fmap(); g=n.fmap(); r=n.qmap()
    active=frozenset(q[b] for b in n.domain)
    domain=frozenset(a for a in m.domain if f[a] in active)
    nodes={('y',y) for y in active}|{('z',z) for z in n.blocks}
    cs=components(nodes,[(('y',q[b]),('z',g[b])) for b in n.domain])
    # A pushout class is encoded by its nonempty target-C block.
    block_of={node: frozenset(c for c in n.target if ('z',r[c]) in comp)
              for node,comp in cs.items()}
    outblocks=frozenset(block_of.values())
    return Mixed(m.source,n.target,domain,outblocks,
                 tuple((a,block_of[('y',f[a])]) for a in sorted(domain))).validate()


def expanded_relation(m,n):
    q=m.qmap(); g=n.fmap()
    return frozenset((q[b],c) for b in n.domain for c in g[b])


def predicted_relation(m,n):
    expanded_closed=dfclosure(expanded_relation(m,n)); f=m.fmap()
    return frozenset((a,c) for a in m.domain for y,c in expanded_closed if f[a]==y)


def powerset(xs):
    xs=tuple(xs)
    for k in range(len(xs)+1):
        for ss in combinations(xs,k): yield frozenset(ss)


def partitions(xs):
    xs=tuple(xs)
    if not xs:
        yield frozenset(); return
    x,*tail=xs
    for p in partitions(tail):
        yield p|{frozenset([x])}
        for block in p: yield (p-{block})|{block|{x}}


def presentations(a,b):
    for qs in partitions(sorted(b)):
        for dom in powerset(sorted(a)):
            d=sorted(dom)
            for images in product(tuple(qs),repeat=len(d)):
                yield Mixed(a,b,dom,qs,tuple(zip(d,images))).validate()


def fixture(a,b,domain,blocks,run):
    ps=frozenset(frozenset(x) for x in blocks)
    return Mixed(frozenset(a),frozenset(b),frozenset(domain),ps,
                 tuple((x,frozenset(v)) for x,v in run.items())).validate()


def main():
    A=frozenset(range(2)); B=frozenset(range(3)); C=frozenset(range(2))
    ms=list(presentations(A,B)); ns=list(presentations(B,C)); count=tight=0
    for m in ms:
        check(difunctional(relation(m)), 'presentation is not difunctional')
        for n in ns:
            count+=1
            rr=compose_rel(relation(m),relation(n)); result=relation(then(m,n))
            check(result==predicted_relation(m,n), 'expanded closure formula')
            check(rr <= result, 'normalization loses relational edge')
            check(dfclosure(rr) <= result, 'normalization not difunctional overapproximation')
            check(difunctional(result), 'normalization output not difunctional')
            active={m.qmap()[b] for b in n.domain}
            if active <= set(m.fmap().values()):
                tight+=1; check(result==dfclosure(rr), 'tight closure formula')
    # Every finite difunctional relation has a canonical presentation.
    rcount=0
    allpairs=[(a,b) for a in A for b in B]
    for rr in powerset(allpairs):
        check(difunctional(dfclosure(rr)), 'closure not difunctional')
        check(rr<=dfclosure(rr), 'closure not extensive')
        check(dfclosure(dfclosure(rr))==dfclosure(rr), 'closure not idempotent')
        if difunctional(rr):
            rcount+=1
            rows={a:frozenset(b for x,b in rr if x==a) for a in A}
            used=frozenset(v for v in rows.values() if v)
            occupied=frozenset().union(*used) if used else frozenset()
            p=Mixed(A,B,frozenset(a for a in A if rows[a]),
                    used|frozenset(frozenset([b]) for b in B-occupied),
                    tuple((a,rows[a]) for a in sorted(A) if rows[a])).validate()
            check(relation(p)==rr, 'canonical representation')
    # Non-descent of binary normalization through relation forgetting.
    fine=fixture(['a'],[0,1,2],['a'],[[0],[1],[2]],{'a':[0]})
    coarse=fixture(['a'],[0,1,2],['a'],[[0],[1,2]],{'a':[0]})
    g=fixture([0,1,2],['c0','c1'],[0,1,2],[['c0'],['c1']],
              {0:['c0'],1:['c0'],2:['c1']})
    check(relation(fine)==relation(coarse), 'input relations differ')
    check(relation(then(fine,g))==frozenset([('a','c0')]), 'fine output')
    check(relation(then(coarse,g))==frozenset([('a','c0'),('a','c1')]), 'coarse output')
    # Original associativity failure, and the associative relational answer.
    f=fixture(['a0','a1'],['b0','b1','b2','b3'],['a0','a1'],
              [['b0','b1'],['b2','b3']],{'a0':['b0','b1'],'a1':['b2','b3']})
    g=fixture(['b0','b1','b2','b3'],['c0','c1','c2'],['b0','b1','b2','b3'],
              [['c0'],['c1'],['c2']],{'b0':['c0'],'b1':['c1'],'b2':['c1'],'b3':['c2']})
    h=fixture(['c0','c1','c2'],['*'],['c2'],[['*']],{'c2':['*']})
    left=relation(then(then(f,g),h)); right=relation(then(f,then(g,h)))
    relational=compose_rel(compose_rel(relation(f),relation(g)),relation(h))
    check(relational==compose_rel(relation(f),compose_rel(relation(g),relation(h))), 'Rel associativity')
    check(left==frozenset([('a0','*'),('a1','*')]), 'left normalized')
    check(right==relational==frozenset([('a1','*')]), 'right/relational')
    check(not difunctional(compose_rel(relation(f),relation(g))), 'middle relation should not be difunctional')
    print(f'Exhaustive normal-form pairs checked: {count}; active-tight pairs: {tight}')
    print(f'Difunctional relations represented on 2x3 carrier: {rcount}')
    print('Expanded-closure formula, overapproximation, tight closure and canonical presentation checks passed.')
    print('Binary non-descent: same input relation, normalized outputs {c0} versus {c0,c1}.')
    print('Three-stage normalization: left {a0,a1}, right {a1}; ordinary Rel: {a1} in both groupings.')
    print('All checks passed.')

if __name__=='__main__': main()
