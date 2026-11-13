"""Exact small-context checks, using integer bit masks as labelled subsets."""

from collections import deque
from itertools import combinations, product
from math import comb

from check_threshold import require


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            return
        sub = (sub - 1) & mask


def closure_system(columns, top):
    result = {top}
    for column in columns:
        result.update({closed & column for closed in tuple(result)})
    return frozenset(result)


def close(subset, family, top):
    result = top
    for closed in family:
        if subset & closed == subset:
            result &= closed
    return result


def row_classes(columns, n):
    classes = {}
    for q in range(n):
        signature = tuple(int(bool(column & (1 << q))) for column in columns)
        classes.setdefault(signature, []).append(q)
    return tuple(tuple(block) for block in classes.values())


def meet_irreducibles(family, top):
    return frozenset(
        member for member in family if member != top
        and not any(left != member and right != member and left & right == member for left in family for right in family)
    )


def all_contexts(n):
    supports = tuple(range(1 << n))
    if n <= 3:
        for mask in range(1 << len(supports)):
            yield tuple(s for i, s in enumerate(supports) if mask & (1 << i))
    else:
        for size in range(4):
            yield from combinations(supports, size)


def check_partial_columns():
    results = []
    no_split_growth_example = None
    for n in range(1, 5):
        top = (1 << n) - 1
        context_count = partial_count = completion_count = closed_completion_count = certain_closed_count = 0
        complete_update_count = split_bound_count = restriction_count = 0
        for columns in all_contexts(n):
            context_count += 1
            family = closure_system(columns, top)
            for partial in product((0, 1, 2), repeat=n):
                # 0 = negative, 1 = positive, 2 = unqueried.
                positive = sum(1 << i for i, value in enumerate(partial) if value == 1)
                negative = sum(1 << i for i, value in enumerate(partial) if value == 0)
                unknown = top ^ positive ^ negative
                completions = tuple(positive | subset for subset in submasks(unknown))
                closed_completions = [subset for subset in completions if subset in family]
                criterion = close(positive, family, top) & negative == 0
                require(bool(closed_completions) == criterion, "Partial-column closed-completion criterion fails")
                upper = top ^ negative
                certainty_criterion = upper in family and all((upper ^ (1 << q)) in family for q in range(n) if unknown & (1 << q))
                require((len(closed_completions) == len(completions)) == certainty_criterion, "Partial-column certainty criterion fails")
                if criterion:
                    require(close(positive, family, top) in closed_completions, "Claimed minimum closed completion fails")
                partial_count += 1
                completion_count += len(completions)
                closed_completion_count += len(closed_completions)
                certain_closed_count += certainty_criterion

            old_classes = row_classes(columns, n)
            for added in range(1 << n):
                new_family = closure_system(columns + (added,), top)
                predicted = family | {member & added for member in family}
                require(new_family == predicted, "One-column meet-closure update formula fails")
                splits = sum(any(added & (1 << q) for q in block) and any(not added & (1 << q) for q in block) for block in old_classes)
                new_classes = row_classes(columns + (added,), n)
                require(len(new_classes) - len(old_classes) == splits, "Row split increment formula fails")
                growth = len(new_family) - len(family)
                require(growth >= splits, "Extent growth is smaller than row split count")
                if n >= 2 and len(old_classes) == n and growth and no_split_growth_example is None:
                    no_split_growth_example = {
                        "n": n, "old_columns_bitmasks": columns, "added_column_bitmask": added,
                        "old_extents_bitmasks": sorted(family), "new_extents_bitmasks": sorted(new_family),
                        "old_row_classes": old_classes, "row_splits": splits, "new_extent_count": growth,
                    }
                complete_update_count += 1
                split_bound_count += 1

            irreducibles = meet_irreducibles(family, top)
            # Literal restriction of the full intent family is tested directly.
            intent_values = {
                sum(1 << j for j, col in enumerate(columns) if subset & col == subset)
                for subset in range(1 << n)
            }
            for retain_mask in range(1 << len(columns)):
                retained = tuple(col for j, col in enumerate(columns) if retain_mask & (1 << j))
                same_closure = closure_system(retained, top) == family
                injective = len({intent & retain_mask for intent in intent_values}) == len(intent_values)
                retains_irreducibles = irreducibles.issubset(retained)
                require(same_closure == injective == retains_irreducibles, "Literal restriction equivalences fail")
                restriction_count += 1
        results.append({
            "n": n,
            "context_scope": "All column-support subfamilies" if n <= 3 else "All column-support subfamilies of size at most three",
            "contexts_checked": context_count,
            "partial_columns_checked": partial_count,
            "partial_column_completion_pairs_checked": completion_count,
            "closed_completions_found": closed_completion_count,
            "partial_columns_with_every_completion_closed": certain_closed_count,
            "fully_measured_column_updates_checked": complete_update_count,
            "row_split_lower_bound_checks": split_bound_count,
            "literal_attribute_restrictions_checked": restriction_count,
        })
    return {"enumerations": results, "separated_rows_with_growing_extent_family": no_split_growth_example}


def preimage(transition, support):
    return sum(1 << q for q, image in enumerate(transition) if support & (1 << image))


def support_orbit(transitions, accepting):
    words = {accepting: ""}
    pending = deque([accepting])
    while pending:
        support = pending.popleft()
        for letter, transition in transitions.items():
            new = preimage(transition, support)
            if new not in words:
                words[new] = letter + words[support]
                pending.append(new)
    return words


def check_dynamic_saturation():
    results = []
    for n, alphabet_size in ((1, 1), (2, 1), (3, 1), (4, 1), (2, 2)):
        top = (1 << n) - 1
        functions = tuple(product(range(n), repeat=n))
        machines = families = saturating = failing = 0
        for generators in product(functions, repeat=alphabet_size):
            transitions = {chr(ord("a") + i): fn for i, fn in enumerate(generators)}
            for accepting in range(1 << n):
                orbit = tuple(support_orbit(transitions, accepting))
                ideal = closure_system(orbit, top)
                machines += 1
                for mask in range(1 << (len(orbit) - 1)):
                    retained = (accepting,) + tuple(s for i, s in enumerate(orbit[1:]) if mask & (1 << i))
                    family = closure_system(retained, top)
                    extensions = {preimage(fn, support) for fn in generators for support in retained}
                    criterion = extensions.issubset(family)
                    require(criterion == (family == ideal), "Finite dynamic saturation criterion fails")
                    families += 1
                    saturating += criterion
                    failing += not criterion
        results.append({
            "n": n, "alphabet_size": alphabet_size, "labelled_machines_and_outputs": machines,
            "retained_support_families_containing_empty_word_support": families,
            "saturating_families": saturating, "failing_families": failing,
        })
    return results


def run_word(transitions, q, word):
    for letter in word:
        q = transitions[letter][q]
    return q


def check_permutation_examples():
    results = []
    for n in (2, 4, 8):
        top = (1 << n) - 1
        m, k = n.bit_length() - 1, n // 2
        transitions = {"c": tuple((q + 1) % n for q in range(n)), "t": tuple(1 if q == 0 else 0 if q == 1 else q for q in range(n))}
        coordinates = tuple(sum(1 << q for q in range(n) if q & (1 << j)) for j in range(m))
        accepting = coordinates[0]
        words = support_orbit(transitions, accepting)
        require(len(words) == comb(n, k), "Wrong permutation support orbit size")
        require(set(words) == {support for support in range(1 << n) if support.bit_count() == k}, "Orbit misses a k-subset")
        full = closure_system(words, top)
        small = closure_system(coordinates, top)
        require(full == {support for support in range(1 << n) if support.bit_count() <= k} | {top}, "Wrong full closure")
        require(len(small) == n and len(row_classes(coordinates, n)) == n, "Coordinate tests fail to separate rows or have wrong closure")
        require(meet_irreducibles(full, top) == set(words), "Wrong indispensable-support family")
        suffixes = tuple(words[support] for support in coordinates)
        histories = tuple("c" * q for q in range(n))
        queries = sorted({h + middle + suffix for h in histories for middle in ("", "c", "t") for suffix in suffixes}, key=lambda w: (len(w), w))
        rows = {tuple(int(bool(accepting & (1 << run_word(transitions, 0, h + w)))) for w in suffixes): q for q, h in enumerate(histories)}
        require(len(rows) == n, "Conformance certificate does not distinguish n states")
        for q, h in enumerate(histories):
            for letter in transitions:
                row = tuple(int(bool(accepting & (1 << run_word(transitions, 0, h + letter + w)))) for w in suffixes)
                require(rows[row] == transitions[letter][q], "Conformance table reconstructs wrong transition")
        polynomial_length_bound = (n + 1) * n * (n - 1) // 2
        require(max(map(len, suffixes)) <= polynomial_length_bound, "Suffix length exceeds stated bound")
        require(len(queries) <= 3 * n * m, "Query count exceeds stated bound")
        require(max(map(len, queries)) <= polynomial_length_bound + n, "Run length exceeds stated bound")
        results.append({
            "n": n, "predictive_states": len(rows), "separating_tests": len(suffixes),
            "separating_words": suffixes, "observed_extents": len(small), "ideal_extents": len(full),
            "indispensable_supports": len(words), "actual_distinct_reset_queries": len(queries),
            "actual_total_executed_intervention_letters": sum(map(len, queries)),
            "actual_maximum_query_length": max(map(len, queries)),
            "query_bound_3_n_log2_n": 3 * n * m,
            "query_words": queries,
        })
    return results


def run():
    return {
        "partial_incidence_columns": check_partial_columns(),
        "finite_dynamic_saturation": check_dynamic_saturation(),
        "permutation_separation_vs_retention": check_permutation_examples(),
    }
