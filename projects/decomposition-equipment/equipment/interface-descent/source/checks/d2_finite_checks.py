"""Independent finite D2 checks; standard library, explicit checks survive -O.

Finite evidence only. All cardinality bounds are reported in run().
"""
from collections import Counter
from itertools import product
from math import prod


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def maps_to(n, bound=2):
    return tuple(f for m in range(bound + 1) for f in product(range(n), repeat=m))


def relations(a, b):
    cells = tuple(product(range(a), range(b)))
    return tuple(frozenset(c for i, c in enumerate(cells) if mask >> i & 1)
                 for mask in range(1 << len(cells)))


def old_paths(rels):
    paths = tuple((a, b) for a, b in sorted(rels[0]))
    for rel in rels[1:]:
        paths = tuple(xs + (b,) for xs in paths for a, b in sorted(rel)
                      if xs[-1] == a)
    return paths


def restricted(relation, left, right):
    return frozenset((i, j) for i, a in enumerate(left) for j, b in enumerate(right)
                     if (a, b) in relation)


def path_comparison(rels, fs, mutation=None):
    """Actually enumerate source and target; do not infer either from criterion."""
    old = old_paths(rels)
    source = old_paths(tuple(restricted(r, f, g) for r, f, g in
                             zip(rels, fs, fs[1:])))
    target = tuple((a, xs, c) for a, fa in enumerate(fs[0]) for xs in old
                   for c, fc in enumerate(fs[-1]) if (fa, fc) == (xs[0], xs[-1]))
    image = tuple((ys[0], tuple(f[y] for f, y in zip(fs, ys)), ys[-1])
                  for ys in source)
    require(set(image) <= set(target), 'comparison does not map into target')
    lhs = {(ys[0], ys[-1]) for ys in source}
    rhs = {(a, c) for a, _, c in target}
    if mutation == 'ignore_internal_image':
        lhs = rhs
    require(lhs <= rhs, 'relational inclusion')
    feasible = {}
    for a, xs, c in target:
        feasible.setdefault((a, c), []).append(xs)
    hit = all(any(all(xs[i] in fs[i] for i in range(1, len(fs)-1))
                  for xs in choices) for choices in feasible.values())
    require((lhs == rhs) == hit, 'feasible witness image criterion')
    fibres = Counter(image)
    for a, xs, c in target:
        expected = prod(sum(y == xs[i] for y in fs[i]) for i in range(1, len(fs)-1))
        require(fibres[(a, xs, c)] == expected, 'actual comparison fibre product')
    bijective = len(source) == len(target) and len(set(image)) == len(target)
    unique_lifts = all(fibres[t] == 1 for t in target)
    if mutation == 'existence_is_bijection':
        unique_lifts = lhs == rhs
    require(bijective == unique_lifts, 'span unique-lift criterion')
    return {'equal': lhs == rhs, 'bijective': bijective, 'source': len(source),
            'target': len(target), 'fibres': sorted(fibres[t] for t in target)}


def exhaustive_paths(length, mutation=None):
    # n=2: every old/primed cardinality <=2. n=3: old endpoints <=1,
    # old internal cardinalities <=2, every primed cardinality <=2.
    old_domains = [range(3)] * (length+1)
    if length == 3:
        old_domains[0] = old_domains[-1] = range(2)
    map_count = relation_count = equal_count = bijective_count = fibre_count = 0
    uniform_cache = {}
    for sizes in product(*old_domains):
        all_rels = tuple(relations(a, b) for a, b in zip(sizes, sizes[1:]))
        for fs in product(*(maps_to(n) for n in sizes)):
            uniform = True
            for rels in product(*all_rels):
                result = path_comparison(rels, fs, mutation)
                uniform &= result['equal']
                relation_count += 1
                equal_count += result['equal']
                bijective_count += result['bijective']
                fibre_count += result['target']
            expected = (not fs[0] or not fs[-1] or
                        any(n == 0 for n in sizes[1:-1]) or
                        all(set(fs[i]) == set(range(sizes[i]))
                            for i in range(1, length)))
            if mutation == 'omit_empty_exceptions':
                expected = all(set(fs[i]) == set(range(sizes[i]))
                               for i in range(1, length))
            require(uniform == expected, 'uniform path criterion with empty exceptions')
            map_count += 1
            uniform_cache[(sizes, fs)] = uniform
    return {'length': length, 'map_families': map_count,
            'relation_map_cases': relation_count, 'relation_equal_cases': equal_count,
            'span_bijective_cases': bijective_count, 'target_witness_fibres': fibre_count,
            'old_cardinality_bounds': [max(x) for x in old_domains],
            'primed_cardinality_bound': 2}, uniform_cache


def global_families(cache):
    # Two named interface types, including repetition of any type in a profile.
    cases = 0
    for sizes in product(range(3), repeat=2):
        for fs in product(*(maps_to(n) for n in sizes)):
            positive = all(cache[(tuple(sizes[i] for i in types),
                                  tuple(fs[i] for i in types))]
                           for types in product(range(2), repeat=3))
            nullary = all(len(set(f)) == len(f) for f in fs)
            all_empty = all(not f for f in fs)
            surjective = all(set(f) == set(range(n)) for n, f in zip(sizes, fs))
            bijective = surjective and nullary
            require(positive == (all_empty or surjective), 'global positive-arity boundary')
            require((positive and nullary) == (all_empty or bijective), 'global all-arity boundary')
            cases += 1
    return {'two_named_type_map_families': cases,
            'all_type_triples_checked_per_family': 8}


def boundary_cases(mutation=None):
    full = (frozenset({(0, 0), (0, 1)}), frozenset({(0, 0), (1, 0)}))
    examples = {}
    for name, internal in [('surjective_noninjective', (0, 0, 1)),
                           ('nonsurjective_relation_still_equal', (0,)),
                           ('equal_cardinality_noniso', (0, 0)),
                           ('bijection', (1, 0))]:
        examples[name] = path_comparison(full, ((0,), internal, (0,)), mutation)
    missed = (frozenset({(0, 1)}), frozenset({(1, 0)}))
    examples['strict_inclusion'] = path_comparison(missed, ((0,), (0,), (0,)), mutation)
    require(not examples['strict_inclusion']['equal'], 'missing needed witness must be strict')
    require(examples['equal_cardinality_noniso'] ==
            {'equal': True, 'bijective': False, 'source': 2, 'target': 2, 'fibres': [0, 2]},
            'equal cardinality cannot replace actual comparison isomorphism')
    path = (frozenset({(0, 1)}), frozenset({(1, 1)}), frozenset({(1, 0)}))
    fs = ((0,), (0,), (0,), (0,))
    adjacent = [path_comparison(path[i:i+2], fs[i:i+3]) for i in range(2)]
    whole = path_comparison(path, fs)
    require(all(x['equal'] and x['bijective'] and x['target'] == 0 for x in adjacent)
            and not whole['equal'], 'adjacent-vacuity is not all-run exactness')
    examples['adjacent_vacuity'] = {'adjacent': adjacent, 'whole': whole}
    nullaries = []
    unary_cases = 0
    for n in range(3):
        for f in maps_to(n):
            diag = {(x, x) for x in range(len(f))}
            kernel_pair = {(x, y) for x, y in product(range(len(f)), repeat=2) if f[x] == f[y]}
            require(diag <= kernel_pair, 'nullary comparison inclusion')
            require((diag == kernel_pair) == (len(set(f)) == len(f)), 'nullary injectivity')
            nullaries.append({'old_size': n, 'map': list(f), 'source': len(diag),
                              'target': len(kernel_pair), 'equal': diag == kernel_pair})
        for m in range(3):
            for f, g, r in product(maps_to(n), maps_to(m), relations(n, m)):
                z = path_comparison((r,), (f, g))
                require(z['equal'] and z['bijective'], 'unary transport comparison')
                unary_cases += 1
    return {'examples': examples, 'nullary_maps': nullaries, 'unary_cases': unary_cases}


def compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for first in range(1, n-k+2):
            for rest in compositions(n-first, k-1):
                yield (first,) + rest


def trees(n, start=0):
    if n == 1:
        yield start
    else:
        for k in range(2, n+1):
            for sizes in compositions(n, k):
                starts = [start + sum(sizes[:i]) for i in range(k)]
                for children in product(*(tuple(trees(s, a)) for s, a in zip(sizes, starts))):
                    yield children


def tree_checks():
    # Repeated leaves literally share a span source, but remain separate slots.
    shared = {'a': (0, 0), 'b': (0, 0)}
    checks = witnesses = 0
    shape_counts = {}
    for n in range(1, 6):
        leaves = [shared] * n
        old = tuple(product(*[tuple(s) for s in leaves]))
        for mult in (0, 1, 2):
            fs = [(0,)] + [tuple(0 for _ in range(mult)) for _ in range(n-1)] + [(0,)]
            restricted_leaves = [tuple((a, x, b) for a in range(len(fs[i]))
                                       for x in leaves[i] for b in range(len(fs[i+1])))
                                 for i in range(n)]
            flat_source = tuple(xs for xs in product(*restricted_leaves)
                                if all(xs[i][-1] == xs[i+1][0] for i in range(n-1)))
            flat_map = {xs: (xs[0][0], tuple(x[1] for x in xs), xs[-1][-1]) for xs in flat_source}
            target = {(0, xs, 0) for xs in old}
            for tree in trees(n):
                def evaluate(t):
                    if isinstance(t, int):
                        return [(x, (x,), x[0], x[-1]) for x in restricted_leaves[t]]
                    out = []
                    for cs in product(*(evaluate(c) for c in t)):
                        if all(cs[i][3] == cs[i+1][2] for i in range(len(cs)-1)):
                            out.append((tuple(c[0] for c in cs),
                                        sum((c[1] for c in cs), ()), cs[0][2], cs[-1][3]))
                    return out
                evaluated = evaluate(tree)
                require({x[1] for x in evaluated} == set(flat_source), 'nested-to-flat comparison domain')
                require(len(evaluated) == len(flat_source), 'nested flattening is bijective')
                c = Counter((left, tuple(x[1] for x in flat), right)
                            for _, flat, left, right in evaluated)
                require(all(c[t] == mult ** (n-1) for t in target), 'tree fibre product')
                require(all(flat_map[flat] == (left, tuple(x[1] for x in flat), right)
                            for _, flat, left, right in evaluated), 'tree comparison coherence')
                checks += 1
                witnesses += len(evaluated)
        shape_counts[str(n)] = len(tuple(trees(n)))
    # One internal interface source must be shared by adjacent occurrences.
    # Separate source lifts (0,1) with equal old value do NOT form a source path.
    fs = ((0,), (0, 0), (0,))
    rels = (frozenset({(0, 0)}),) * 2
    result = path_comparison(rels, fs)
    require(result['source'] == 2 and result['target'] == 1,
            'shared intermediate source must not become independent four lifts')
    return {'all_planar_reduced_tree_shapes_by_leaves': shape_counts,
            'tree_shape_multiplicity_cases': checks, 'nested_witnesses': witnesses,
            'internal_lift_multiplicities': [0, 1, 2],
            'repeated_leaf_source': 'same actual two-apex span, separate occurrence slots',
            'shared_intermediate_source_lifts': 2,
            'scope': 'all reduced ordered shapes through five leaves; not an all-tree proof'}


def run(mutation=None):
    boundaries = boundary_cases(mutation)
    binary, cache = exhaustive_paths(2, mutation)
    ternary, _ = exhaustive_paths(3, mutation)
    return {'binary_exhaustive': binary, 'ternary_exhaustive': ternary,
            'global_map_families': global_families(cache),
            'boundaries': boundaries, 'trees': tree_checks()}
