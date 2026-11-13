"""Finite models and obstructions accompanying ApprehensionEnrichments.lean."""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Lens:
    source: int
    target: int
    get: tuple
    put: tuple


def lid(n):
    return Lens(n, n, tuple(range(n)), tuple(tuple(range(n)) for _ in range(n)))


def lc(g, f):
    assert f.target == g.source
    return Lens(f.source, g.target,
                tuple(g.get[f.get[s]] for s in range(f.source)),
                tuple(tuple(f.put[s][g.put[f.get[s]][w]] for w in range(g.target))
                      for s in range(f.source)))


def lawful(f, overwrite=False):
    return all(f.put[s][f.get[s]] == s for s in range(f.source)) and all(
        f.get[f.put[s][v]] == v for s in range(f.source) for v in range(f.target)
    ) and (not overwrite or all(
        f.put[f.put[s][v]][w] == f.put[s][w]
        for s in range(f.source) for v in range(f.target) for w in range(f.target)))


def projection(source_bits, target_bits):
    suffix = 2 ** (source_bits - target_bits)
    return Lens(2 ** source_bits, 2 ** target_bits,
                tuple(s // suffix for s in range(2 ** source_bits)),
                tuple(tuple(v * suffix + s % suffix for v in range(2 ** target_bits))
                      for s in range(2 ** source_bits)))


@dataclass(frozen=True)
class LApp:
    deriv: Lens
    occ: Lens

    def __post_init__(self):
        assert self.deriv.target == self.occ.target


def lj(f):
    return LApp(f, lid(f.target))


def reground(i, j, h):
    assert i.deriv.source == j.occ.source
    assert lc(h, j.occ) == i.deriv
    return LApp(lc(h, j.deriv), i.occ)


def lens_checks():
    l0 = projection(2, 1)
    l1 = Lens(4, 2, l0.get,
              tuple(tuple(2 * v + ((s % 2) ^ (s // 2) ^ v) for v in range(2))
                    for s in range(4)))
    candidates = []
    for changed_suffixes in product(range(2), repeat=4):
        put = tuple(tuple(s if v == s // 2 else 2 * v + changed_suffixes[s]
                          for v in range(2)) for s in range(4))
        f = Lens(4, 2, l0.get, put)
        assert lawful(f)
        candidates.append(f)
    strong = [f for f in candidates if lawful(f, True)]
    assert set(strong) == {l0, l1}
    assert l0.get == l1.get and l0 != l1
    # Any lift h of the raw identity on two bits is forced by PutGet to lid(2).
    identity_lifts = [Lens(2, 2, (0, 1), tuple((a, b) for a, b in rows))
                     for rows in product(tuple(product(range(2), repeat=2)), repeat=2)]
    identity_lifts = [h for h in identity_lifts if lawful(h)]
    assert identity_lifts == [lid(2)]
    assert not any(lc(h, l1) == l0 for h in identity_lifts)
    f, g, h = projection(3, 2), l0, Lens(2, 2, (1, 0), ((1, 0), (1, 0)))
    assert all(lawful(x, True) for x in (f, g, h))
    assert lc(lc(h, g), f) == lc(h, lc(g, f))
    assert reground(lj(g), lj(f), g) == lj(lc(g, f))
    i = LApp(l0, l1)
    j = LApp(projection(3, 2), lid(4))
    k = LApp(projection(4, 3), lid(8))
    left = reground(reground(i, j, l0), k, lc(l0, j.deriv))
    right = reground(i, reground(j, k, j.deriv), l0)
    assert left == right and left.occ == i.occ
    assert all(lc(lid(x.target), x) == x == lc(x, lid(x.source)) for x in (f, g, h))
    print('Lenses: 16 lifts of the same get; exactly two satisfy PutPut; raw identity support between them has no lens lift.')
    print('Lens canonical composition, units, associativity, and noncanonical supported associativity passed.')


@dataclass(frozen=True)
class Model:
    states: tuple
    contexts: tuple
    interventions: tuple
    idle: object
    responses: tuple


@dataclass(frozen=True)
class CMap:
    source: Model
    target: Model
    state: tuple
    context: tuple
    intervention: tuple


def cc(g, f):
    assert f.target == g.source
    return CMap(f.source, g.target,
                tuple(g.state[x] for x in f.state),
                tuple(g.context[x] for x in f.context),
                tuple(g.intervention[x] for x in f.intervention))


def causal_law(f):
    m, n = f.source, f.target
    return f.intervention[m.interventions.index(m.idle)] == n.interventions.index(n.idle) and all(
        f.state[m.responses[u][i]] == n.responses[f.context[u]][f.intervention[i]]
        for u in range(len(m.contexts)) for i in range(len(m.interventions)))


def bit_model(n):
    states = tuple(product((0, 1), repeat=n))
    interventions = tuple(product((None, 0, 1), repeat=n))
    responses = tuple(tuple(states.index(tuple(u[k] if i[k] is None else i[k] for k in range(n)))
                            for i in interventions) for u in states)
    return Model(states, states, interventions, (None,) * n, responses)


def prefix(m, n, count):
    return CMap(m, n, tuple(n.states.index(x[:count]) for x in m.states),
                tuple(n.contexts.index(x[:count]) for x in m.contexts),
                tuple(n.interventions.index(x[:count]) for x in m.interventions))


def causal_checks():
    m3, m2, m1 = (bit_model(n) for n in (3, 2, 1))
    f, g = prefix(m3, m2, 2), prefix(m2, m1, 1)
    h = CMap(m1, m1, (1, 0), (1, 0), (0, 2, 1))
    assert all(causal_law(x) for x in (f, g, h, cc(g, f), cc(h, cc(g, f))))
    assert cc(g, f) == prefix(m3, m1, 1)
    assert cc(cc(h, g), f) == cc(h, cc(g, f))
    for x in (f, g, h, cc(g, f)):
        assert set(x.state) == set(range(len(x.target.states)))
        assert set(x.context) == set(range(len(x.target.contexts)))
        assert set(x.intervention) == set(range(len(x.target.interventions)))
    states = tuple(product((0, 1), repeat=2))
    interventions = (None, 0, 1)
    chain = Model(states, (0, 1), interventions, None,
                  tuple(tuple(states.index((u if i is None else i, u if i is None else i))
                              for i in interventions) for u in (0, 1)))
    common = Model(states, (0, 1), interventions, None,
                   tuple(tuple(states.index((u if i is None else i, u))
                               for i in interventions) for u in (0, 1)))
    assert all(chain.responses[u][0] == common.responses[u][0] for u in (0, 1))
    lifts = [CMap(chain, common, tuple(range(4)), beta, (0,) + tail)
             for beta in product(range(2), repeat=2) for tail in product(range(3), repeat=2)]
    assert len(lifts) == 36 and not any(causal_law(f) for f in lifts)
    print('Causal projections 3 bits -> 2 -> 1 and a nonidentity recoding commute, compose associatively, and preserve surjectivity.')
    print('Causal obstruction: all 36 idle-preserving lifts of the observational identity fail.')


if __name__ == '__main__':
    lens_checks()
    causal_checks()
