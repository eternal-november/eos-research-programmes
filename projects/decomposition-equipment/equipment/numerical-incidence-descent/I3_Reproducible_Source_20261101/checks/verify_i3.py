#!/usr/bin/env python3
"""Independent finite I3 checks. No imported F3/F4 implementation; no asserts.

Sets throughout, with every actual vertex occurrence labelled by [v].
The prescribed target Z retains ordered block sizes, not actual placements.
Run `python verify_i3.py`; intentional mutants exit nonzero, also under -O.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb, factorial, prod
import json
from pathlib import Path
import sys


class VerificationFailure(RuntimeError):
    pass


def require(condition, description):
    if not condition:
        raise VerificationFailure(description)


@dataclass(frozen=True, order=True)
class Graph:
    v: int
    mask: int

    def __post_init__(self):
        require(self.v >= 0 and 0 <= self.mask < (1 << comb(self.v, 2)),
                f"invalid graph: {self}")


@lru_cache(None)
def graph_edges(g):
    return frozenset(e for i, e in enumerate(combinations(range(g.v), 2))
                     if (g.mask >> i) & 1)


def graph_from_edges(v, edges):
    edges = frozenset(tuple(sorted(e)) for e in edges)
    pairs = tuple(combinations(range(v), 2))
    require(edges <= set(pairs), "edge outside supplied vertex carrier")
    return Graph(v, sum(1 << i for i, e in enumerate(pairs) if e in edges))


@lru_cache(None)
def induced(g, vertices):
    require(tuple(sorted(set(vertices))) == vertices, "restriction is not increasing")
    require(all(0 <= x < g.v for x in vertices), "restriction vertex outside graph")
    edges = graph_edges(g)
    return graph_from_edges(len(vertices),
                            ((i, j) for i, j in combinations(range(len(vertices)), 2)
                             if (vertices[i], vertices[j]) in edges))


@dataclass(frozen=True)
class Cut:
    graph: Graph
    slots: tuple[int, ...]  # each vertex's original input occurrence
    path: tuple[int, ...]  # objects of the actual category [2]

    @property
    def degree(self):
        return len(self.path) - 1


@dataclass(frozen=True)
class SizeCut:
    sizes: tuple[int, ...]
    path: tuple[int, ...]


def validate(x):
    require(len(x.slots) == x.graph.v, "vertex assignment has wrong cardinality")
    require(len(x.path) >= 1 and tuple(sorted(x.path)) == x.path,
            "noncomposable poset arrow path")
    require(all(a in (0, 1, 2) for a in x.path), "unknown interface")
    require(all(0 <= s < x.degree for s in x.slots), "slot outside profile")


def graphs(v):
    return (Graph(v, m) for m in range(1 << comb(v, 2)))


def paths(n):
    return combinations_with_replacement(range(3), n + 1)


def cuts(g, n):
    for slots in product(range(n), repeat=g.v):
        for path in paths(n):
            yield Cut(g, slots, path)


def monotone(m, n):
    return combinations_with_replacement(range(n + 1), m + 1)


def active(alpha, n):
    return alpha[0] == 0 and alpha[-1] == n


def pull(x, alpha):
    """Actual contravariant graph/partition restriction, including outer faces."""
    n = x.degree
    require(len(alpha) >= 1 and tuple(sorted(alpha)) == alpha,
            "nonmonotone simplex operator")
    require(0 <= alpha[0] <= alpha[-1] <= n, "simplex operator out of bounds")
    keep = tuple(v for v, s in enumerate(x.slots) if alpha[0] <= s < alpha[-1])
    new_slots = tuple(next(j for j in range(len(alpha) - 1)
                          if alpha[j] <= x.slots[v] < alpha[j + 1]) for v in keep)
    return Cut(induced(x.graph, keep), new_slots, tuple(x.path[i] for i in alpha))


def q(x):
    return SizeCut(tuple(x.slots.count(i) for i in range(x.degree)), x.path)


def zpull(z, alpha):
    return SizeCut(tuple(sum(z.sizes[alpha[j]:alpha[j + 1]])
                         for j in range(len(alpha) - 1)),
                   tuple(z.path[i] for i in alpha))


def edge_forget(x):
    return Cut(Graph(x.graph.v, 0), x.slots, x.path)


def multinomial(parts):
    return factorial(sum(parts)) // prod(factorial(x) for x in parts)


def predicted_lifts(z, alpha):
    return prod(multinomial(z.sizes[alpha[j]:alpha[j + 1]])
                for j in range(len(alpha) - 1))


def check_simplicial():
    naturality = 0
    composition = 0
    source_count = 0
    for v in range(4):
        for g in graphs(v):
            for n in range(4):
                alphas = tuple(a for m in range(4) for a in monotone(m, n))
                for x in cuts(g, n):
                    validate(x)
                    source_count += 1
                    for a in alphas:
                        y = pull(x, a)
                        validate(y)
                        require(q(y) == zpull(q(x), a), "q is not simplicial")
                        require(edge_forget(y) == pull(edge_forget(x), a),
                                "actual F4 map is not simplicial")
                        naturality += 2
                    # Independently compose every operator with m,l <= 2.
                    if v <= 2:
                        for m in range(3):
                            for a in monotone(m, n):
                                for ell in range(3):
                                    for b in monotone(ell, m):
                                        ab = tuple(a[i] for i in b)
                                        require(pull(pull(x, a), b) == pull(x, ab),
                                                "actual simplicial composition failed")
                                        require(zpull(zpull(q(x), a), b) == zpull(q(x), ab),
                                                "size target simplicial composition failed")
                                        composition += 2
    return {"graphs_vertices": [0, 3], "degree": [0, 3],
            "source_simplices": source_count, "naturality_equalities": naturality,
            "composition_equalities": composition,
            "composition_vertices": [0, 2], "intermediate_and_final_degrees": [0, 2]}


def check_active_fibres(mutation):
    bins = 0
    f4_bins = 0
    nonsingletons = 0
    for v in range(4):
        for g in graphs(v):
            for n in range(4):
                xs = tuple(cuts(g, n))
                for m in range(4):
                    for a in monotone(m, n):
                        if not active(a, n):
                            continue
                        fibres = Counter((pull(x, a), q(x)) for x in xs)
                        f4 = Counter((pull(x, a), edge_forget(x)) for x in xs)
                        for (_, z), count in fibres.items():
                            expected = predicted_lifts(z, a)
                            if mutation == "collapse_lifts":
                                expected = 1
                            require(count == expected, "active q fibre multiplicity mismatch")
                            nonsingletons += count > 1
                            bins += 1
                        require(all(c == 1 for c in f4.values()), "F4 active fibre not singleton")
                        f4_bins += len(f4)
    # Independent surjectivity test: enumerate every possible pullback pair,
    # rather than only the image of a source simplex. Include degeneracies.
    pullback_pairs = 0
    size_pullback_pairs = 0
    for v in range(3):
        for g in graphs(v):
            for m in range(3):
                coarse = tuple(cuts(g, m))
                for n in range(4):
                    fine_targets = tuple(cuts(Graph(v, 0), n))
                    fine_source = tuple(cuts(g,n))
                    # Construct Z directly from weak compositions, NOT from
                    # the image of enumerated source cuts. Missing bins fail.
                    size_targets = tuple(SizeCut(s,p) for s in weak_compositions(v,n)
                                         for p in paths(n))
                    for a in monotone(m, n):
                        if not active(a, n):
                            continue
                        size_fibres = Counter((pull(x,a),q(x)) for x in fine_source)
                        for old in coarse:
                            for fine_size in size_targets:
                                if q(old) != zpull(fine_size,a):
                                    continue
                                count=size_fibres[(old,fine_size)]
                                require(count==predicted_lifts(fine_size,a) and count>0,
                                        "q prescribed pullback pair has missing/wrong lifts")
                                size_pullback_pairs += 1
                            for fine in fine_targets:
                                if edge_forget(old) != pull(fine, a):
                                    continue
                                lifted = Cut(g, fine.slots, fine.path)
                                validate(lifted)
                                require(pull(lifted, a) == old and edge_forget(lifted) == fine,
                                        "F4 prescribed pullback inverse failed")
                                pullback_pairs += 1
    require(nonsingletons > 0, "no genuine objective-failure witness tested")
    return {"vertices": [0, 3], "fine_and_coarse_degrees": [0, 3],
            "q_fibres": bins, "q_nonsingleton_fibres": nonsingletons,
            "F4_singleton_fibres": f4_bins, "F4_independent_pullback_pairs": pullback_pairs,
            "q_independent_size_pullback_pairs":size_pullback_pairs,
            "independent_pullback_vertices": [0, 2], "independent_coarse_degrees": [0, 2]}


def actual_binary(g, start, end, observation):
    out = Counter()
    for middle in range(start, end + 1):
        for slots in product(range(2), repeat=g.v):
            us = tuple(i for i, s in enumerate(slots) if s == 0)
            vs = tuple(i for i, s in enumerate(slots) if s == 1)
            out[(observation(induced(g, us), start, middle),
                 observation(induced(g, vs), middle, end))] += 1
    return out


def size_observation(g, start, end):
    return g.v, start, end


def edge_count_observation(g, start, end):
    return g.v, g.mask.bit_count(), start, end


def delta(size, start, end, weighted=True):
    return {((k, start, middle), (size-k, middle, end)):
            comb(size, k) if weighted else 1
            for middle in range(start, end+1) for k in range(size+1)}


def coassoc_terms(basis, weighted, left):
    out = Counter()
    for (x, y), c in delta(*basis, weighted).items():
        for (a, b), d in delta(*(x if left else y), weighted).items():
            out[(a, b, y) if left else (x, a, b)] += c*d
    return out


def check_coefficients(mutation):
    representative_checks = 0
    formula_checks = 0
    prior = {}
    native_mismatches = 0
    for v in range(5):
        for g in graphs(v):
            for start, end in combinations_with_replacement(range(3), 2):
                actual = actual_binary(g, start, end, size_observation)
                expected = delta(v, start, end, mutation != "unit_coefficients")
                require(actual == expected, "actual aggregate binomial coefficients fail")
                formula_checks += len(actual)
                key = (v, start, end)
                if key in prior:
                    require(actual == prior[key], "aggregate depends on representative graph")
                    representative_checks += 1
                prior[key] = actual
                native_mismatches += actual != delta(v, start, end, False)
    require(native_mismatches > 0, "native target difference not observed")
    coassociativity = 0
    correction = 0
    for v in range(13):
        for start, end in combinations_with_replacement(range(3), 2):
            for weighted in (False, True):
                require(coassoc_terms((v,start,end), weighted, True) ==
                        coassoc_terms((v,start,end), weighted, False),
                        "coassociativity failed")
                coassociativity += 1
                terms = delta(v,start,end,weighted)
                left = Counter()
                right = Counter()
                for (a,b), c in terms.items():
                    if a[0] == 0 and a[1] == a[2]:
                        left[b] += c
                    if b[0] == 0 and b[1] == b[2]:
                        right[a] += c
                require(left == right == Counter({(v,start,end):1}), "counit failed")
            for (a,b), c in delta(v,start,end,True).items():
                weight = (lambda n:n+1) if mutation == "wrong_factorial" else factorial
                require(c*weight(a[0])*weight(b[0]) == weight(v),
                        "factorial coalgebra conjugacy failed")
                correction += 1
    # At v=2 the diagonal basis coefficient 2 is nonunit over Z and zero in F2.
    require(factorial(2) == 2 and factorial(2) % 2 == 0, "integral/F2 limitation missing")
    return {"all_graph_vertices": [0,4], "actual_formula_coefficient_checks":formula_checks,
            "same_q1_representative_comparisons":representative_checks,
            "source_wholes_disagreeing_with_native_Z":native_mismatches,
            "formula_size_domain":[0,12], "coassociativity_cases":coassociativity,
            "factorial_conjugacy_terms":correction,
            "automorphism_weights":"none: all carriers are labelled finite sets"}


def compositions(total):
    if total == 0:
        yield ()
        return
    for cuts_ in product((0,1), repeat=total-1):
        acc = 1
        out = []
        for cut in cuts_:
            if cut:
                out.append(acc)
                acc=1
            else:
                acc += 1
        yield tuple(out+[acc])


def cluster_graph(rows):
    edges=[]
    offset=0
    for r in rows:
        edges.extend(combinations(range(offset,offset+r),2))
        offset += r
    return graph_from_edges(offset, edges)


def occupancy(rows, slots, n):
    out=[]
    offset=0
    for r in rows:
        out.append(tuple(slots[offset:offset+r].count(k) for k in range(n)))
        offset += r
    return tuple(out)


def matrix_pull(matrix, alpha):
    rows = [tuple(sum(row[alpha[j]:alpha[j+1]]) for j in range(len(alpha)-1))
            for row in matrix]
    return tuple(row for row in rows if sum(row))


def cluster_rows(g):
    if not g.v:
        return ()
    # Derive components independently from literal edges; reject non-cluster graphs.
    edges=graph_edges(g)
    unseen=set(range(g.v))
    components=[]
    while unseen:
        todo=[min(unseen)]
        seen=set()
        while todo:
            x=todo.pop()
            if x in seen:
                continue
            seen.add(x)
            todo.extend(y for y in unseen if y != x and tuple(sorted((x,y))) in edges)
        unseen-=seen
        require(all((a,b) in edges for a,b in combinations(sorted(seen),2)),
                "component not a clique")
        require(max(seen)-min(seen)+1 == len(seen), "component not contiguous")
        components.append(len(seen))
    return tuple(components)


def check_cluster():
    bins=0
    matrices=0
    restrictions=0
    six_vertex_nontrivial=0
    for v in range(7):
        for rows in compositions(v):
            g=cluster_graph(rows)
            require(cluster_rows(g)==rows,"cluster graph encoding mismatch")
            w=prod(factorial(r) for r in rows)
            for n in (1,2,3):
                counts=Counter(occupancy(rows,s,n) for s in product(range(n),repeat=v))
                for matrix, count in counts.items():
                    expected=prod(multinomial(row) for row in matrix)
                    require(count==expected,"cluster actual occupancy multiplicity fails")
                    child_weight=prod(factorial(matrix[b][k])
                                      for b in range(len(rows)) for k in range(n))
                    require(count*child_weight==w,"cluster factorial correction fails")
                    bins += 1
                    if rows==(3,2,1) and n==3 and count>1:
                        six_vertex_nontrivial += 1
                if v<=4:
                    for slots in product(range(n),repeat=v):
                        # Full path (0,...,0,2) includes mixed interfaces when n>=2.
                        path=tuple([0]*n+[2])
                        x=Cut(g,slots,path)
                        matrix=occupancy(rows,slots,n)
                        for m in range(3):
                            for a in monotone(m,n):
                                y=pull(x,a)
                                actual=occupancy(cluster_rows(y.graph),y.slots,m)
                                require(actual==matrix_pull(matrix,a),
                                        "cluster occupancy outer restriction failed")
                                restrictions += 1
                matrices += len(counts)
    require(six_vertex_nontrivial>0,"six-vertex mixed cluster model not exercised")
    return {"all_contiguous_clique_compositions_vertices":[0,6],"degrees":[1,3],
            "actual_occupancy_fibres":bins,"factorial_correction_fibres":matrices,
            "simplicial_restriction_vertices":[0,4],"restriction_checks":restrictions,
            "K3_K2_K1_nontrivial_ternary_fibres":six_vertex_nontrivial}


def block_group(rows):
    blocks=[]
    offset=0
    for r in rows:
        blocks.append(tuple(permutations(range(offset,offset+r))))
        offset+=r
    return tuple(tuple(y for block in pieces for y in block) for pieces in product(*blocks))


def permutation_action(slots,permutation):
    out=[-1]*len(slots)
    for v,w in enumerate(permutation):
        out[w]=slots[v]
    return tuple(out)


def check_RE_regime_orbits():
    rows=(3,2,1)
    cluster=cluster_graph(rows)
    complement=Graph(cluster.v,((1<<comb(cluster.v,2))-1)^cluster.mask)
    fixtures=(
        ('trivial_P4',graph_from_edges(4,[(0,1),(1,2),(2,3)]),(1,1,1,1)),
        ('contiguous_cluster_3_2_1',cluster,rows),
        ('complementary_contiguous_multipartite_3_2_1',complement,rows),
        ('homogeneous_complete_4',Graph(4,(1<<6)-1),(4,)),
        ('homogeneous_edgeless_4',Graph(4,0),(4,)),
    )
    report=[]
    for name,g,group_rows in fixtures:
        group=block_group(group_rows)
        orbit_count=0
        partitions=0
        action_checks=0
        for n in (1,2,3):
            remaining=set(product(range(n),repeat=g.v))
            while remaining:
                representative=min(remaining)
                orbit={permutation_action(representative,p) for p in group}
                require(orbit<=remaining,"distinct computed permutation orbits overlap")
                remaining-=orbit
                matrix=occupancy(group_rows,representative,n)
                child_group_order=prod(factorial(a) for row in matrix for a in row)
                stabilizer=sum(permutation_action(representative,p)==representative
                               for p in group)
                require(stabilizer==child_group_order,"R/E stabilizer product mismatch")
                require(len(orbit)*child_group_order==len(group),
                        "R/E actual orbit weight mismatch")
                original_inputs=tuple(induced(g,tuple(v for v,s in enumerate(representative)
                                                       if s==k)) for k in range(n))
                for changed in orbit:
                    inputs=tuple(induced(g,tuple(v for v,s in enumerate(changed) if s==k))
                                 for k in range(n))
                    require(inputs==original_inputs,"orbit action changes retained profile")
                    action_checks+=1
                partitions+=len(orbit)
                orbit_count+=1
        report.append({'fixture':name,'vertices':g.v,'group_order':len(group),
                       'degrees':[1,3],'actual_orbits':orbit_count,
                       'actual_partitions':partitions,'profile_preservation_checks':action_checks})
    return {'scope':'selected literal fixtures in all four inherited R/E regimes, not classification',
            'formula':'|H_G| = |orbit(partition)| * product_i |H_(G|U_i)|',
            'fixtures':report}


def check_coefficient_instability():
    examples=[]
    for v in range(4,13):
        star=graph_from_edges(v,[(0,1),(0,2),(0,3)])
        path=graph_from_edges(v,[(0,1),(1,2),(2,3)])
        require(edge_count_observation(star,0,2)==edge_count_observation(path,0,2),
                "unstable observations have different whole classes")
        cs=actual_binary(star,0,2,edge_count_observation)
        cp=actual_binary(path,0,2,edge_count_observation)
        key=((1,0,0,0),(v-1,0,0,2))
        require(cs[key]==1 and cp[key]==0,"padded star/path obstruction failed")
        if v==4:
            key2=((3,2,0,0),(1,0,0,2))
            require(cs[key2]==3 and cp[key2]==2,"star/path 3|1 check failed")
        examples.append({"v":v,"whole_edge_count":3,"empty_remainder_star":cs[key],
                         "empty_remainder_path":cp[key]})
    return {"observation":"(vertex_count, edge_count, actual_arrow)",
            "graphs":"K1,3 and P4 padded by v-4 isolated ordered vertices",
            "examples":examples,"v4_3vertex_2edge_coefficients":{"star":3,"path":2}}


def mu_k(start,end):
    return 1 if start==end else -1 if end-start==1 else 0


def convolution(f,g,basis,weighted):
    return sum(c*f(*a)*g(*b) for (a,b),c in delta(*basis,weighted).items())


def check_mobius_and_length(mutation):
    cases=0
    for v in range(13):
        for a,c in combinations_with_replacement(range(3),2):
            epsilon=int(v==0 and a==c)
            for weighted in (False,True):
                def mu(n,s,t):
                    size_factor=(-1)**n if weighted else int(n==0)-int(n==1)
                    return size_factor*mu_k(s,t)
                one=lambda n,s,t:1
                require(convolution(one,mu,(v,a,c),weighted)==epsilon and
                        convolution(mu,one,(v,a,c),weighted)==epsilon,
                        "standard Mobius inversion failed")
                cases += 1
            # Pullback of Z's zeta via factorial conjugacy is factorial, NOT 1.
            weighted_zeta=lambda n,s,t:factorial(n)
            transferred_mu=lambda n,s,t:factorial(n)*(int(n==0)-int(n==1))*mu_k(s,t)
            require(convolution(weighted_zeta,transferred_mu,(v,a,c),True)==epsilon,
                    "transported weighted-zeta inversion failed")
    require((-1)**2 != int(2==0)-int(2==1),"distinct standard Mobius values lost")
    effective=0
    maxes=defaultdict(lambda:-1)
    for v in range(5):
        for n in range(7):
            for sizes in weak_compositions(v,n):
                for path in paths(n):
                    is_effective=all(sizes[i]>0 or path[i]!=path[i+1] for i in range(n))
                    if is_effective:
                        bound=v+path[-1]-path[0]
                        if mutation=="ignore_empty_grade":
                            bound=v
                        require(n<=bound,"effective length bound failed")
                        key=(v,path[0],path[-1])
                        maxes[key]=max(maxes[key],n)
                        effective += 1
    for v in range(5):
        for a,c in combinations_with_replacement(range(3),2):
            require(maxes[(v,a,c)]==v+c-a,"sharp effective length not attained")
    # Normalized units versus primitive unary syntax. An inserted 0/id column
    # is degenerate, unlike 0/nonidentity; this uses the actual grade path.
    base=Cut(Graph(1,0),(0,),(0,2))
    inserted=pull(base,(0,0,1))
    require(q(inserted)==SizeCut((0,1),(0,0,2)),"nullary-unit insertion malformed")
    require(inserted.slots==(1,),"empty slot lost its occurrence position")
    c2=[]
    for m in range(1,21):
        arrows=(1,)*(2*m)
        require(sum(arrows)%2==0 and all(arrows),"C2 unbounded-length witness invalid")
        c2.append(len(arrows))
    return {"size_domain":[0,12],"standard_Mobius_convolution_cases":cases,
            "binomial_mu":"(-1)^v mu_[2](a,c)",
            "native_size_mu":"(delta_v0-delta_v1) mu_[2](a,c)",
            "zeta_warning":"factorial isomorphism pulls native zeta to v!, not to 1",
            "effective_length_vertices":[0,4],"lengths_enumerated":[0,6],
            "effective_simplices":effective,"sharp_maximum":"v+c-a",
            "C2_nonidentity_empty_factor_lengths":c2,
            "raw_unary_syntax":"not counted as extra simplicial effective factors"}


def weak_compositions(v,n):
    if n==0:
        if v==0:
            yield ()
        return
    if n==1:
        yield (v,)
        return
    for x in range(v+1):
        for tail in weak_compositions(v-x,n-1):
            yield (x,)+tail


def check_domain_and_provenance():
    rejected=[]
    malformed=(
        ("nonempty nullary",lambda:validate(Cut(Graph(1,0),(0,),(0,)))),
        ("reversed interface path",lambda:validate(Cut(Graph(1,0),(0,),(2,0)))),
        ("unknown interface",lambda:validate(Cut(Graph(0,0),(),(0,3)))),
        ("out of range occurrence",lambda:validate(Cut(Graph(1,0),(2,),(0,1)))),
        ("unordered restriction",lambda:induced(Graph(2,0),(1,0))),
        ("invalid adjacency mask",lambda:Graph(2,2)),
    )
    for name,run in malformed:
        try:
            run()
        except VerificationFailure:
            rejected.append(name)
        else:
            raise VerificationFailure(f"malformed input accepted: {name}")
    # These are the actual two C5 binary partitions identified by the F3 L
    # equation after F4's edge erasure. No external occurrence exchange occurs.
    edge=Graph(2,1)
    left=Cut(edge,(0,1),(0,1,2))
    swapped=Cut(edge,(1,0),(0,1,2))
    require(left!=swapped and q(left)==q(swapped),"actual placement loss not exhibited")
    require(edge_forget(left)!=edge_forget(swapped),"F4 wrongly forgot placement")
    edgeless=Cut(Graph(2,0),left.slots,left.path)
    require(left!=edgeless and q(left)==q(edgeless),"nontrivial whole coarsening absent")
    # Input graphs are both the same singleton, while actual occurrence slots
    # and the 0->1->2 interface path remain distinct and in their fixed order.
    require(induced(edge,(0,))==induced(edge,(1,)),"repeated input component missing")
    repeated=Cut(edge,(0,1),(1,1,1))
    require(q(repeated).sizes==(1,1) and repeated.path==(1,1,1),
            "identical full graph/grade input components missing")
    zero=Cut(Graph(0,0),(),(1,))
    validate(zero)
    require(q(zero)==SizeCut((),(1,)),"designated nullary unit missing")
    return {"malformed_inputs_rejected":rejected,
            "placement_loss":"(G,(0,1),0->1->2) != (G,(1,0),0->1->2), same q",
            "whole_loss":"edge and edgeless graph with same partition have same q",
            "F4_control":"same two placements remain distinct under edge erasure",
            "repeated_input_component":"two identical (singleton graph,id_1) components",
            "nullary_unit":"empty graph at the retained object 1"}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path)
    parser.add_argument("--mutate", choices=("collapse_lifts","unit_coefficients",
                                            "wrong_factorial","ignore_empty_grade"))
    args=parser.parse_args()
    # Mutants run the relevant independent evaluator immediately, not a guard
    # that merely rejects a flag. Failure is caused by the mathematical check.
    if args.mutate=="collapse_lifts":
        check_active_fibres(args.mutate)
    elif args.mutate in ("unit_coefficients","wrong_factorial"):
        check_coefficients(args.mutate)
    elif args.mutate=="ignore_empty_grade":
        check_mobius_and_length(args.mutate)
    results={"status":"PASS", "evidence_level":"C, finite only",
             "implementation":"independent executable; imports no prior verifier",
             "scope":"actual graph-cut X -> prescribed ordered-size Z; labelled finite sets",
             "domain_and_provenance":check_domain_and_provenance(),
             "simplicial":check_simplicial(),
             "active_fibres":check_active_fibres(None),
             "coefficients":check_coefficients(None),
             "cluster":check_cluster(),
             "RE_regime_orbits":check_RE_regime_orbits(),
             "unstable_control":check_coefficient_instability(),
             "mobius_length":check_mobius_and_length(None)}
    encoded=json.dumps(results,indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded,end="")


if __name__=="__main__":
    try:
        main()
    except VerificationFailure as exc:
        print(f"FAIL: {exc}",file=sys.stderr)
        sys.exit(1)
