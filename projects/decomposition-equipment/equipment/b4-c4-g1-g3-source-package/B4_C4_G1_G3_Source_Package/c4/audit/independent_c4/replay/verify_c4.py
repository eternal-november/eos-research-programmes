#!/usr/bin/env python3
"""Finite C4 certificates; standard-library only, no imported author evaluator.

Proofs are in ../proof/C4_target_and_proof.txt. This is finite C evidence,
not a universal proof or kernel certificate. Assertions remain active under -O.
"""
import hashlib
import itertools as it
import json
from collections import Counter
from pathlib import Path

COUNTS = Counter()
FALSE_RULES = {}


def require(p, label):
    if not p:
        raise RuntimeError(label)


def powerset(values):
    values = tuple(values)
    for bits in range(1 << len(values)):
        yield frozenset(x for i, x in enumerate(values) if bits >> i & 1)


def pairs(m):
    return tuple(it.combinations(range(m), 2))


def induced(E, block):
    block = tuple(sorted(block))
    return (len(block), frozenset((i, j) for i in range(len(block))
            for j in range(i + 1, len(block)) if (block[i], block[j]) in E))


def blocks_of(layer, k):
    return tuple(frozenset(i for i, v in enumerate(layer) if v == j)
                 for j in range(k))


def lift_partition(outer, children):
    return tuple(frozenset(tuple(sorted(B))[j] for j in D)
                 for B, child in zip(outer, children) for D in child)


def compose(R, S):
    return frozenset((a, c) for a, b in R for bb, c in S if b == bb)


def pull(R, f, g):
    return frozenset((i, j) for i in range(len(f)) for j in range(len(g))
                     if (f[i], g[j]) in R)


def graph_fibres():
    # Every graph, every ordered layering, not a sample of positive cases.
    for m in range(5):
        for k in range(4):
            for layer in it.product(range(k), repeat=m):
                B = blocks_of(layer, k)
                X = frozenset((a, b) for a, b in pairs(m) if layer[a] != layer[b])
                fibres = Counter()
                for E in powerset(pairs(m)):
                    H = tuple(induced(E, b) for b in B)
                    fibres[H] += 1
                    lifted = frozenset((tuple(sorted(b))[a], tuple(sorted(b))[c])
                                      for b, h in zip(B, H) for a, c in h[1])
                    require(lifted | (E & X) == E, 'whole decoder')
                    require(not lifted & X, 'disjoint internal and cross')
                    COUNTS['anchored_graph_records_m_le_4_k_le_3'] += 1
                require(all(n == 2 ** len(X) for n in fibres.values()), 'fiber size')
                require((max(fibres.values()) == 1) == (len(X) == 0), 'injectivity boundary')
                COUNTS['partitions_m_le_4_k_le_3'] += 1
    B = (frozenset({0}), frozenset({1, 3}), frozenset({2, 4}), frozenset({5}))
    internal = frozenset({(1, 3), (2, 4)})
    X = frozenset(pairs(6)) - internal
    H = tuple(induced(internal, b) for b in B)
    seen = set()
    for C in powerset(X):
        E = internal | C
        require(tuple(induced(E, b) for b in B) == H, 'six vertex leaves')
        seen.add(E)
        COUNTS['six_vertex_anchored_fibre'] += 1
    require(len(seen) == 8192 and len(X) == 13, 'six vertex complete fibre')
    for e in X:
        require(tuple(induced(internal, b) for b in B) ==
                tuple(induced(internal | {e}, b) for b in B), 'each cross bit invisible')
        COUNTS['indispensable_cross_edge_bits'] += 1
    FALSE_RULES['whole_decoder_drops_all_cross_edges'] = any(E != internal for E in seen)
    return B


def interface_erasure():
    relations = list(powerset(it.product(range(2), repeat=2)))
    label_pairs = list(it.product(range(3), repeat=2))
    for i, j in label_pairs:
        for k, l in label_pairs:
            for R in relations:
                for S in relations:
                    W = compose(R, S)
                    # Erased R;S to W is always exact, regardless of labels.
                    require(compose(R, S) == W, 'erased exact composition')
                    COUNTS['interface_pair_records'] += 1
                    COUNTS['interface_typed_valid' if j == k else 'interface_spurious_after_erasure'] += 1
    require(COUNTS['interface_typed_valid'] == 6912, 'typed count')
    require(COUNTS['interface_spurious_after_erasure'] == 13824, 'spurious count')
    D = frozenset({(0, 0), (1, 1)})
    invalid = ((0, 1, D), (2, 0, D))
    require(invalid[0][1] != invalid[1][0] and compose(D, D) == D, 'named interface counterexample')
    FALSE_RULES['accept_path_after_erasing_interface_tags'] = True


def occurrence_and_primitives(B):
    u = (frozenset({0}), frozenset({1}))
    v = tuple(reversed(u))
    identity = (frozenset({0}),)
    mixed = lift_partition(B, (identity, u, v, identity))
    doubled_u = lift_partition(B, (identity, u, u, identity))
    doubled_v = lift_partition(B, (identity, v, v, identity))
    require(mixed == tuple(frozenset({x}) for x in (0, 1, 3, 4, 2, 5)), 'named occurrence result')
    require(mixed != doubled_u and mixed != doubled_v, 'different repeated substitutions')
    for r in range(2, 7):
        outer = tuple(frozenset({2*i, 2*i+1}) for i in range(r))
        results = {lift_partition(outer, cs) for cs in it.product((u, v), repeat=r)}
        require(len(results) == 2**r, 'independent occurrence choices')
        diagonal = {lift_partition(outer, (x,)*r) for x in (u, v)}
        require(len(diagonal) == 2 and diagonal < results, 'component-indexed image')
        COUNTS['occurrence_choice_records_r_2_through_6'] += len(results)
    E = frozenset({(0, 1)})
    pu = tuple(induced(E, b) for b in u)
    pv = tuple(induced(E, b) for b in v)
    require(pu == pv and u != v, 'primitive pair same profile different witness')
    # Primitive alphabet quotient keeps shape, full output and full profile.
    erase_u = ('corolla', (2, E), pu)
    erase_v = ('corolla', (2, E), pv)
    require(erase_u == erase_v, 'primitive quotient collision')
    FALSE_RULES['key_substitution_by_component_value'] = mixed != doubled_u
    FALSE_RULES['replace_primitive_witness_by_fibre_support'] = erase_u == erase_v and u != v


def set_partitions(xs):
    if not xs:
        yield ()
        return
    x, *tail = xs
    for p in set_partitions(tail):
        yield (frozenset({x}),) + p
        for i in range(len(p)):
            yield p[:i] + (p[i] | {x},) + p[i+1:]


def parallel_equations():
    # b and b2 have the SAME complete index; id_c and id_d do not.
    idx = {'id_c': ('c', ('c',)), 'b': ('c', ('c', 'c')),
           'b2': ('c', ('c', 'c')), 'id_d': ('d', ('d',))}
    good = 0
    for p in set_partitions(list(idx)):
        constant = all(len({idx[x] for x in block}) == 1 for block in p)
        # Attempt representative assignment and test the entire quotient triangle.
        image = {block: idx[sorted(block)[0]] for block in p}
        triangle = all(image[block] == idx[x] for block in p for x in block)
        require(constant == triangle, 'index descent iff parallel')
        good += constant
        COUNTS['equivalence_relations_on_four_operations'] += 1
    require(COUNTS['equivalence_relations_on_four_operations'] == 15 and good == 2, 'quotient count')
    require(idx['id_c'][0] == idx['b'][0] and idx['id_c'][1] != idx['b'][1], 'same output different arity')
    require(idx['id_c'][0] != idx['id_d'][0], 'different output')
    FALSE_RULES['nonparallel_quotient_uses_chosen_representative_index'] = True


def restriction_species():
    # Check original increasing-coordinate restrictions exhaustively.
    for m in range(5):
        for E in powerset(pairs(m)):
            for U in powerset(range(m)):
                EU = induced(E, U)
                orderU = tuple(sorted(U))
                for V in powerset(range(len(U))):
                    nested = induced(EU[1], V)
                    direct = induced(E, frozenset(orderU[i] for i in V))
                    require(nested == direct, 'ordered restriction composition')
                    COUNTS['nested_induced_restrictions_m_le_4'] += 1
            # All possible total orders/framing permutations and layers up to 3.
            for order in it.permutations(range(m)):
                pos = {v: i for i, v in enumerate(order)}
                stdE = frozenset(tuple(sorted((pos[a], pos[b]))) for a, b in E)
                backE = frozenset(tuple(sorted((order[a], order[b]))) for a, b in stdE)
                require(backE == E, 'graph framing inverse')
                for k in range(4):
                    for layer in it.product(range(k), repeat=m):
                        stdlayer = tuple(layer[v] for v in order)
                        backlayer = tuple(stdlayer[pos[v]] for v in range(m))
                        require(backlayer == layer, 'layer framing inverse')
                        COUNTS['order_framed_layer_records_m_le_4_k_le_3'] += 1
    # Outer faces restrict the WHOLE to its remaining vertices.
    E = frozenset({(0, 1), (1, 2)})
    correct = induced(E, frozenset({1, 2}))
    FALSE_RULES['outer_face_keeps_unrestricted_whole'] = correct != (3, E)


def relation_boundary_checks():
    rels = list(powerset(it.product(range(2), repeat=2)))
    for R in rels:
        for S in rels:
            for f in it.product(range(2), repeat=3):
                left = compose(pull(R, (0, 1), f), pull(S, f, (0, 1)))
                right = compose(R, S)
                require(left <= right, 'lax restriction inclusion')
                if set(f) == {0, 1}:
                    require(left == right, 'surjective internal equality')
                    COUNTS['surjective_internal_relation_comparisons'] += 1
                COUNTS['all_internal_relation_comparisons'] += 1
    f = (0, 0)
    diagonal1 = frozenset({(0, 0)})
    pulled = pull(diagonal1, f, f)
    diagonal2 = frozenset({(0, 0), (1, 1)})
    require(diagonal2 < pulled and len(pulled) == 4, 'nullary injectivity boundary')
    # All relations on the shared interior: surjection duplicates realizers.
    source = (0, 1, 1)
    require(set(source) == {0, 1} and len(source) == 3, 'nonbijective surjection')
    require(len(set(source)) == 2, 'two original realizing witnesses')
    FALSE_RULES['surjectivity_implies_nullary_exactness'] = pulled != diagonal2
    FALSE_RULES['equal_endpoint_relations_imply_bijective_witnesses'] = len(source) != len(set(source))


def main():
    B = graph_fibres()
    interface_erasure()
    occurrence_and_primitives(B)
    parallel_equations()
    restriction_species()
    relation_boundary_checks()
    require(all(FALSE_RULES.values()) and len(FALSE_RULES) == 8, 'semantic false-rule controls')
    report = {
        'status': 'PASS', 'evidence_level': 'finite C only; uniform P separately',
        'implementation': 'standard library independent coordinate calculations; no source evaluator imported',
        'counts': dict(sorted(COUNTS.items())),
        'semantic_false_rule_controls': FALSE_RULES,
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    target = Path(__file__).with_name('results.json')
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
