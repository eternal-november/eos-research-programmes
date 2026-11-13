#!/usr/bin/env python3
"""Independent finite proof regressions; no simulator imports or outcome experiment."""
from fractions import Fraction as F
from itertools import product
import json


def hazard(windows, d):
    frames = sorted(set().union(*map(set, windows)))
    risk = F(0)
    for bits in product((0, 1), repeat=len(frames)):
        bad = dict(zip(frames, bits))
        prob = F(1)
        for bit in bits:
            prob *= F(1, 50) if bit else F(49, 50)
        accepted = []
        for window in windows:
            noise = sum((F(-1 if bad[f] else 1, 32) for f in window), F(0))/2
            accepted.append(d + noise - F(1, 32) <= F(3, 4))
        # First work slot, second work slot, and final delayed tail.
        violation = False
        for t in range(3):
            for i in range(5):
                own = accepted[i] if t < 2 else 0
                prev = accepted[(i-1)%5] if t > 0 else 0
                violation |= d + F(1, 2)*own + F(1, 4)*prev > F(3, 2)
        if d == F(77, 100):
            assert violation == any(bits)
        risk += prob*violation
    return risk


class JoinTree:
    """Boolean exact messages; dirty by actual cut-side dependency, not value delta."""
    adj = {0: (1, 2, 3), 1: (0,), 2: (0,), 3: (0,)}
    scopes = {0: (0,), 1: (0, 1), 2: (0, 2), 3: (0, 3)}
    def __init__(self):
        self.mode = {v: 0 for v in self.adj}
        self.cache = {}
        self.dirty = {(u,v) for u in self.adj for v in self.adj[u]}
        for edge in list(self.dirty):
            self.msg(*edge)
    def local(self, node, a):
        mode = self.mode[node]
        return mode == 0 or (mode == 1 and a[0] == 0) or (mode == 2 and a[0] == 1) or (mode == 3 and a[0] == a[node])
    def side(self, u, v):
        result, stack = {u}, [u]
        while stack:
            x = stack.pop()
            for y in self.adj[x]:
                if y != v and y not in result:
                    result.add(y); stack.append(y)
        return result
    def update(self, node, mode):
        self.mode[node] = mode
        for u in self.adj:
            for v in self.adj[u]:
                if node in self.side(u, v):
                    self.dirty.add((u, v))
    def msg(self, u, v):
        if (u,v) not in self.dirty:
            return self.cache[u,v]
        incoming = [self.msg(n,u) for n in self.adj[u] if n != v]
        result = set()
        for vals in product((0,1), repeat=len(self.scopes[u])):
            a = dict(zip(self.scopes[u],vals))
            if self.local(u,a) and all(a[0] in m for m in incoming):
                result.add(a[0])
        self.cache[u,v] = result
        self.dirty.discard((u,v))
        return result
    def query(self,q):
        incoming = [self.msg(n,q) for n in self.adj[q]]
        return {vals for vals in product((0,1),repeat=len(self.scopes[q]))
                if self.local(q,dict(zip(self.scopes[q],vals))) and all(vals[0] in m for m in incoming)}
    def exact(self,q):
        return {tuple(a[v] for v in self.scopes[q]) for a in product((0,1),repeat=4)
                if all(self.local(n,a) for n in self.adj)}


def main():
    aligned = [(-2,-1)]*5
    shifted = [(-2,-1)]*3+[(-1,0)]*2
    assert hazard(aligned,F(77,100)) == F(99,2500)
    assert hazard(shifted,F(77,100)) == F(7351,125000)
    assert hazard(aligned,F(1,2)) == hazard(shifted,F(1,2)) == 0
    assert F(99,2500) < F(1,20) < F(7351,125000)

    # Same report, different recursive successor: report average is not observer state.
    histories = [(0,1),(1,0)]
    assert len({sum(h)/2 for h in histories}) == 1
    assert len({F(h[-1],2) for h in histories}) == 2
    # Same marginals do not preserve joint domains or persistent-world constraints.
    eq, neq = {(0,0),(1,1)}, {(0,1),(1,0)}
    assert all({x[i] for x in eq} == {x[i] for x in neq} for i in (0,1))
    assert not neq <= eq
    # Selecting after revealing two Bernoulli signs raises mission risk above p.
    assert 1-F(49,50)**2 == F(99,2500) > F(1,50)

    # Demonstrate the obsolete single-path-only cache failure exactly.
    t = JoinTree()
    t.update(1,1)
    assert t.query(2) == {(0,0),(0,1)}
    stale_center_to_3 = t.cache[0,3].copy()
    assert stale_center_to_3 == {0,1} and t.exact(3) == {(0,0),(0,1)}
    # Retraction restores possibilities; another branch's change does not erase dirty state.
    t.update(2,2)
    assert t.query(3) == t.exact(3) == set()
    t.update(1,0)
    assert t.query(1) == t.exact(1) == {(1,0),(1,1)}

    # All depth-three leaf updates, including narrowing, widening and contradictions,
    # interleaved with arbitrary query locations. Compare each query to global enumeration.
    operations = list(product((1,2,3),range(4),range(4)))
    checked = 0
    def walk(tree,depth):
        nonlocal checked
        if not depth: return
        from copy import deepcopy
        for node,mode,q in operations:
            nxt = deepcopy(tree)
            nxt.update(node,mode)
            assert nxt.query(q) == nxt.exact(q)
            checked += 1
            walk(nxt,depth-1)
    walk(JoinTree(),3)
    print(json.dumps({'status':'PASS','exact_aligned_risk':str(F(99,2500)),
          'exact_misaligned_risk':str(F(7351,125000)),
          'sequential_update_query_checks':checked,
          'scope':'finite mathematical audit, not acquisition or outcome experiment'},indent=2))

if __name__ == '__main__': main()
