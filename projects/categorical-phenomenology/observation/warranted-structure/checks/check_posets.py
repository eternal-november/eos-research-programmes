"""Exact finite checks for the order/meet examples; Python standard library only."""

from itertools import combinations, product


def require(condition, explanation):
    """Keep checks enabled even under `python -O`."""
    if not condition:
        raise RuntimeError(explanation)


class Poset:
    def __init__(self, elements, relation):
        self.elements = tuple(elements)
        self.relation = frozenset(relation)

    @classmethod
    def from_strict_generators(cls, elements, edges):
        elements = tuple(elements)
        relation = set(edges) | {(x, x) for x in elements}
        while True:
            expanded = relation | {
                (x, z) for x, y in relation for y2, z in relation if y == y2
            }
            if expanded == relation:
                return cls(elements, relation)
            relation = expanded

    def le(self, x, y):
        return (x, y) in self.relation

    def valid(self):
        return (
            all(self.le(x, x) for x in self.elements)
            and all(x == y or not self.le(y, x) for x, y in self.relation)
            and all(
                self.le(x, z)
                for x, y in self.relation
                for y2, z in self.relation
                if y == y2
            )
        )

    def lower_bounds(self, a, b):
        return tuple(x for x in self.elements if self.le(x, a) and self.le(x, b))

    def meet(self, a, b):
        lower = self.lower_bounds(a, b)
        greatest = [x for x in lower if all(self.le(y, x) for y in lower)]
        require(len(greatest) <= 1, "The input relation is not a poset")
        return greatest[0] if greatest else None

    def all_binary_meets(self):
        return all(self.meet(a, b) is not None for a in self.elements for b in self.elements)

    def matrix(self, elements=None):
        elements = self.elements if elements is None else tuple(elements)
        return [[int(self.le(x, y)) for y in elements] for x in elements]


def preserves_induced_order(old, new):
    return all(old.le(x, y) == new.le(x, y) for x in old.elements for y in old.elements)


def labelled_posets(n):
    """Enumerate every labelled order once, not only naturally labelled orders."""
    elements = tuple(range(n))
    pairs = tuple(combinations(elements, 2))
    for choices in product((0, 1, 2), repeat=len(pairs)):
        relation = {(x, x) for x in elements}
        for (a, b), choice in zip(pairs, choices):
            if choice == 1:
                relation.add((a, b))
            elif choice == 2:
                relation.add((b, a))
        candidate = Poset(elements, relation)
        if candidate.valid():
            yield candidate


def add_new_meet(old, a, b):
    require(not old.le(a, b) and not old.le(b, a), "Construction requires incomparability")
    w = "new"
    require(w not in old.elements, "Fresh point is already present")
    relation = set(old.relation) | {(w, w)}
    relation.update((x, w) for x in old.elements if old.le(x, a) and old.le(x, b))
    relation.update((w, y) for y in old.elements if old.le(a, y) or old.le(b, y))
    return Poset(old.elements + (w,), relation), w


def check_order_examples():
    a = Poset.from_strict_generators(("z", "a", "b"), (("z", "a"), ("z", "b")))
    b = Poset.from_strict_generators(
        ("z", "a", "b", "w"), (("z", "w"), ("w", "a"), ("w", "b"))
    )
    c = Poset.from_strict_generators(
        ("z", "a", "b", "w"),
        (("z", "a"), ("z", "b"), ("w", "a"), ("w", "b")),
    )
    require(all(p.valid() for p in (a, b, c)), "Explicit relation is not a poset")
    require(preserves_induced_order(a, b) and preserves_induced_order(a, c), "Old order changed")
    require([p.meet("a", "b") for p in (a, b, c)] == ["z", "w", None], "Wrong explicit meet")
    require(all(p.meet("z", "a") == "z" for p in (a, b, c)), "Comparable meet changed")

    counts = {}
    constructed = replaced = supplied = comparable_checks = 0
    for n in range(1, 5):
        orders = tuple(labelled_posets(n))
        counts[str(n)] = len(orders)
        for old in orders:
            for x, y in combinations(old.elements, 2):
                if old.le(x, y) or old.le(y, x):
                    continue
                new, w = add_new_meet(old, x, y)
                require(new.valid(), "The one-point construction is not a poset")
                require(preserves_induced_order(old, new), "One-point construction changed old order")
                require(new.meet(x, y) == w, "New point is not the new meet")
                constructed += 1
                if old.meet(x, y) is None:
                    supplied += 1
                else:
                    replaced += 1
                for u in old.elements:
                    for v in old.elements:
                        if old.le(u, v):
                            require(new.meet(u, v) == u, "Comparable pair not stable")
                            comparable_checks += 1

    require(counts == {"1": 1, "2": 3, "3": 19, "4": 219}, "Incomplete labelled-poset enumeration")

    # Independently inspect every extension order on four labelled points, rather
    # than only the special extensions made by add_new_meet.
    general_extension_checks = 0
    for extension in labelled_posets(4):
        for x in range(3):
            for y in range(3):
                if extension.le(x, y):
                    require(extension.meet(x, y) == x, "Comparable meet changed in general extension")
                    general_extension_checks += 1

    return {
        "explicit_worlds": {
            "old_element_order": list(a.elements),
            "old_comparison_matrix": a.matrix(),
            "A_meet_a_b": a.meet("a", "b"),
            "B_meet_a_b": b.meet("a", "b"),
            "C_meet_a_b": c.meet("a", "b"),
            "B_preserves_all_old_comparisons": preserves_induced_order(a, b),
            "C_preserves_all_old_comparisons": preserves_induced_order(a, c),
            "comparable_meet_z_a_in_A_B_C": [p.meet("z", "a") for p in (a, b, c)],
        },
        "exhaustive_extension_checks": {
            "labelled_poset_counts": counts,
            "incomparable_pair_constructions": constructed,
            "existing_meets_replaced": replaced,
            "previously_absent_meets_supplied": supplied,
            "comparable_pairs_in_constructed_extensions_checked": comparable_checks,
            "comparable_pairs_in_all_four_point_extensions_checked": general_extension_checks,
        },
    }


def graph_poset(n, edge_mask):
    lower = tuple("l%d" % i for i in range(n))
    upper = tuple("u%d" % j for j in range(n))
    elements = ("0",) + lower + upper
    edges = [("0", x) for x in lower + upper]
    edges += [(lower[i], upper[j]) for i in range(n) for j in range(n) if edge_mask & (1 << (i * n + j))]
    return Poset.from_strict_generators(elements, edges)


def has_four_cycle(n, edge_mask):
    neighbors = [sum(1 << i for i in range(n) if edge_mask & (1 << (i * n + j))) for j in range(n)]
    return any((neighbors[j] & neighbors[k]).bit_count() >= 2 for j, k in combinations(range(n), 2))


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            break
        sub = (sub - 1) & mask


def check_graph_certificates():
    results = []
    for n in range(1, 5):
        total_edges = n * n
        free = {mask: not has_four_cycle(n, mask) for mask in range(1 << total_edges)}
        maximum = max(mask.bit_count() for mask, is_free in free.items() if is_free)
        maximum_example = next(mask for mask, is_free in free.items() if is_free and mask.bit_count() == maximum)
        order_checks = certificate_checks = completion_checks = law_checks = 0
        if n <= 3:
            actual = {}
            for mask, is_free in free.items():
                p = graph_poset(n, mask)
                require(p.valid(), "Graph construction failed poset axioms")
                actual[mask] = p.all_binary_meets()
                require(actual[mask] == is_free, "C4 and all-meets conditions differ")
                order_checks += 1
                if actual[mask]:
                    table = {(x, y): p.meet(x, y) for x in p.elements for y in p.elements}
                    require(all(table[x, x] == x for x in p.elements), "Idempotence failed")
                    require(all(table[x, y] == table[y, x] for x in p.elements for y in p.elements), "Commutativity failed")
                    require(all(table[table[x, y], z] == table[x, table[y, z]] for x in p.elements for y in p.elements for z in p.elements), "Associativity failed")
                    law_checks += 1
            certified = []
            for unknown in range(1 << total_edges):
                completions = tuple(submasks(unknown))
                sound = all(actual[mask] for mask in completions)
                completion_checks += len(completions)
                require(sound == free[unknown], "Partial negative transcript criterion failed")
                if sound:
                    certified.append(total_edges - unknown.bit_count())
                certificate_checks += 1
            require(min(certified) == total_edges - maximum, "Minimum negative certificate is incorrect")

        empty = graph_poset(n, 0)
        singleton_checks = 0
        for i in range(n):
            for j in range(n):
                single = graph_poset(n, 1 << (i * n + j))
                require(single.all_binary_meets(), "Singleton-edge completion lacks meets")
                require(empty.meet("l%d" % i, "u%d" % j) == "0", "Empty graph has wrong meet")
                require(single.meet("l%d" % i, "u%d" % j) == "l%d" % i, "Singleton edge did not change target meet")
                singleton_checks += 1

        results.append({
            "n": n,
            "graphs_enumerated": len(free),
            "four_cycle_free_graphs": sum(free.values()),
            "maximum_four_cycle_free_edges": maximum,
            "minimum_negative_certificate_on_empty_graph": total_edges - maximum,
            "example_maximum_edge_matrix": [[int(bool(maximum_example & (1 << (i * n + j)))) for j in range(n)] for i in range(n)],
            "graph_posets_checked_for_meet_equivalence": order_checks,
            "semilattice_laws_checked_on_complete_tables": law_checks,
            "negative_transcripts_checked_against_all_completions": certificate_checks,
            "transcript_completion_pairs_checked": completion_checks,
            "singleton_edge_table_recovery_witnesses": singleton_checks,
        })
    require([row["maximum_four_cycle_free_edges"] for row in results] == [1, 3, 6, 9], "Unexpected small extremal numbers")
    return results


def run():
    return {"orders_and_meets": check_order_examples(), "bipartite_certificate_examples": check_graph_certificates()}
