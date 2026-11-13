#!/usr/bin/env python3
"""Exact finite interpreter/checks for the frozen O6 Case I signature."""
from dataclasses import dataclass
from fractions import Fraction

FUNS = {'id': (0, 1), 'not': (1, 0), 'zero': (0, 0), 'one': (1, 1)}

@dataclass(frozen=True)
class Handle:
    token: str
    kind: str
    epoch: int

class Machine:
    def __init__(self, bit=None):
        self.bit = bit
        self.live = Handle('r', 'U' if bit is None else 'S', 0)
        self.events = []
        self.cost = 0
        self.mass = Fraction(1)
        self.transfers = []

    def take_return(self, h, owner, kind='S'):
        assert h == self.live, 'not the currently owned handle'
        self.transfers.append((owner, h, Handle('r', kind, h.epoch + 1)))
        self.live = Handle('r', kind, h.epoch + 1)
        return self.live

    def primitive(self, op, h):
        assert h == self.live
        if op == 'init':
            assert h.kind == 'U' and self.bit is None
            self.bit, result, charge = 0, None, 0
        elif op == 'commit':
            assert h.kind == 'S' and self.bit in (0, 1)
            self.bit, result, charge = 1, None, 1
        elif op == 'read':
            assert h.kind == 'S' and self.bit in (0, 1)
            result, charge = self.bit, 1
        else:
            raise AssertionError('undeclared method')
        h = self.take_return(h, op)
        self.events.append(op.title())
        self.cost += charge
        return result, h

    def invoke(self, menu, h, enclosing_rank=1, callback_rank=0):
        assert callback_rank < enclosing_rank
        assert menu in FUNS and h.kind == 'S'
        h = self.take_return(h, 'enter callback')
        b, h = self.primitive('read', h)
        h = self.take_return(h, 'return callback')
        return FUNS[menu][b], h

    def run(self, order, menu, initialized=False):
        h = self.live
        if initialized:
            _, h = self.primitive('init', h)
        if order == 'early':
            _, h = self.primitive('commit', h)
            z, h = self.invoke(menu, h)
        elif order == 'late':
            z, h = self.invoke(menu, h)
            # z is ordinary data; only h is passed to commit.
            _, h = self.primitive('commit', h)
        else:
            raise AssertionError('unknown implementation')
        assert h == self.live and h.kind == 'S'
        tree = ('Leaf', z, h.token, h.kind, self.bit)
        for node in reversed(self.events):
            tree = (node, tree)  # unary O1 grafting
        return tree, self.mass, self.cost, (self.bit, h.token, h.kind, self.cost)

def expected(order, b, f, initialized=False):
    body = ('Leaf', FUNS[f][1 if order == 'early' else b], 'r', 'S', 1)
    nodes = ['Commit', 'Read'] if order == 'early' else ['Read', 'Commit']
    for node in reversed(nodes):
        body = (node, body)
    return ('Init', body) if initialized else body

def public(tree):
    if tree[0] == 'Leaf':
        return tree[:-1]
    return tree[0], public(tree[1])

def erase_private_nodes(tree):
    if tree[0] == 'Leaf':
        return tree
    child = erase_private_nodes(tree[1])
    return child if tree[0] in ('Init', 'Commit') else (tree[0], child)

def must_reject(thunk):
    try:
        thunk()
    except AssertionError:
        return
    raise AssertionError('invalid ownership/rank accepted')

rows = 0
for b in (0, 1):
    for f in FUNS:
        results = {}
        for order in ('early', 'late'):
            m = Machine(b)
            r = m.run(order, f)
            assert r[0] == expected(order, b, f)
            assert r[1:3] == (Fraction(1), 2)
            assert r[3] == (1, 'r', 'S', 2)
            # Every handoff invalidates the previous dynamic ownership witness.
            assert all(new.epoch == old.epoch + 1 for _, old, new in m.transfers)
            assert len({old.epoch for _, old, _ in m.transfers}) == len(m.transfers)
            results[order] = r
            rows += 1
        assert results['early'][3] == results['late'][3]
        assert results['early'][0] != results['late'][0]  # full body comparison
        # API repair replaces late's body by exactly early's body.
        assert Machine(b).run('early', f) == results['early']

x = Machine().run('early', 'id', initialized=True)
y = Machine().run('late', 'id', initialized=True)
assert x[0] == expected('early', 0, 'id', True)
assert y[0] == expected('late', 0, 'id', True)
assert erase_private_nodes(public(x[0])) != erase_private_nodes(public(y[0]))
assert x[3] == y[3]
# Singleton native maps and couplings have no alternative support choice.
assert x[1] == y[1] == 1 and public(x[0]) != public(y[0])
m = Machine(0)
old = m.live
m.primitive('read', old)
must_reject(lambda: m.primitive('commit', old))
must_reject(lambda: Machine(0).invoke('id', Handle('r','S',0), 0, 0))
print(f'PASS: {rows} body rows, four callbacks, both initial bits, initialized distinguisher, ownership/rank rejection, exact API repair')

# Separate explicit read-budget signature, not a reinterpretation of State.
class CounterMachine:
    def __init__(self, bit=None):
        self.bit = bit
        self.kind = 'U' if bit is None else 'S1'
        self.epoch = 0
        self.events = []
        self.cost = 0

    def step(self, op, owned_epoch):
        assert owned_epoch == self.epoch, 'stale owned handle'
        if op == 'init':
            assert self.kind == 'U' and self.bit is None
            self.bit, self.kind = 0, 'S1'
            result, charge, label = None, 0, 'Init'
        elif op in ('commit0', 'commit1'):
            assert self.kind == 'S' + op[-1], 'wrong management kind'
            self.bit = 1
            result, charge, label = None, 1, 'Commit'
        elif op == 'read':
            assert self.kind == 'S1', 'read needs positive allowance'
            result, self.kind = self.bit, 'S0'
            charge, label = 1, 'Read'
        else:
            raise AssertionError('undeclared method')
        self.epoch += 1
        self.cost += charge
        self.events.append(label)
        return result, self.epoch

    def callback(self, f, owned_epoch):
        assert f in FUNS and self.kind == 'S1'
        b, h = self.step('read', owned_epoch)
        assert self.kind == 'S0'
        return FUNS[f][b], h

    def run(self, order, f, initialized=False):
        h = self.epoch
        if initialized:
            _, h = self.step('init', h)
        assert self.kind == 'S1'
        if order == 'early':
            _, h = self.step('commit1', h)
            z, h = self.callback(f, h)
        elif order == 'late':
            z, h = self.callback(f, h)
            _, h = self.step('commit0', h)
        else:
            raise AssertionError('unknown implementation')
        assert self.kind == 'S0' and h == self.epoch
        body = ('Leaf', z, 'r', self.kind, self.bit)
        for event in reversed(self.events):
            body = (event, body)
        return body, Fraction(1), self.cost, (self.bit, 'r', self.kind, self.cost)

def counter_endpoint(tree):
    if tree[0] == 'Leaf':
        return tree[:3] + ('S0',) + tree[4:]
    return tree[0], counter_endpoint(tree[1])

counter_rows = 0
for b in (0, 1):
    for f in FUNS:
        results = {}
        for order in ('early', 'late'):
            m = CounterMachine(b)
            result = m.run(order, f)
            assert result[0] == counter_endpoint(expected(order, b, f))
            assert result[1:] == (Fraction(1), 2, (1, 'r', 'S0', 2))
            must_reject(lambda m=m: m.step('read', m.epoch))
            results[order] = result
            counter_rows += 1
        assert results['early'][3] == results['late'][3]
        assert results['early'][0] != results['late'][0]
        assert CounterMachine(b).run('early', f) == results['early']
for order in ('early', 'late'):
    result = CounterMachine().run(order, 'id', initialized=True)
    assert result[0] == counter_endpoint(expected(order, 0, 'id', True))
    assert result[2:] == (2, (1, 'r', 'S0', 2))
m = CounterMachine(0)
must_reject(lambda: m.step('commit0', m.epoch))
_, h = m.step('read', m.epoch)
must_reject(lambda: m.step('commit1', h))
must_reject(lambda: m.step('read', h))
must_reject(lambda: m.step('commit0', 0))
print(f'PASS: {counter_rows} additional countered body rows, two initialized rows, E1-to-F0 endpoints, zero-budget read rejection, management-kind/stale-handle rejection')
