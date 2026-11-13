"""Exact S3, quotient-descent, conformance, and finite-bound examples."""

from collections import Counter, deque
from itertools import combinations, permutations, product

from check_posets import require


ALPHABET = ("a", "b")
IDENTITY = (0, 1, 2)
GENERATORS = {"a": (1, 0, 2), "b": (1, 2, 0)}
H = ("", "a", "b", "bb", "ab", "ba")


def compose(p, q):
    """Permutation convention: (p*q)(i) = p(q(i))."""
    return tuple(p[q[i]] for i in range(3))


def phi(word):
    state = IDENTITY
    for letter in word:
        state = compose(state, GENERATORS[letter])
    return state


def behavior(word):
    return int(phi(word) == IDENTITY)


def words_through(depth):
    return tuple("".join(letters) for length in range(depth + 1) for letters in product(ALPHABET, repeat=length))


def word_key(word):
    return len(word), word


def partition_by_signatures(states, signature):
    blocks = {}
    for state in states:
        blocks.setdefault(signature(state), []).append(state)
    return tuple(tuple(block) for block in blocks.values())


class Machine:
    """Finite complete binary-output machine, initial state 0."""
    def __init__(self, transitions, outputs):
        self.transitions = tuple(tuple(row) for row in transitions)
        self.outputs = tuple(outputs)
        self.n = len(outputs)
        require(len(self.transitions) == self.n, "Wrong transition table size")
        require(all(len(row) == len(ALPHABET) and all(0 <= t < self.n for t in row) for row in self.transitions), "Incomplete transition table")

    def after(self, word, state=0):
        for letter in word:
            state = self.transitions[state][ALPHABET.index(letter)]
        return state

    def output(self, word):
        return self.outputs[self.after(word)]

    def partition(self):
        blocks = partition_by_signatures(range(self.n), lambda q: self.outputs[q])
        while True:
            labels = {q: i for i, block in enumerate(blocks) for q in block}
            refined = partition_by_signatures(
                range(self.n), lambda q: (self.outputs[q], tuple(labels[t] for t in self.transitions[q]))
            )
            if refined == blocks:
                return blocks
            blocks = refined

    def minimal_quotient(self):
        blocks = self.partition()
        labels = {q: i for i, block in enumerate(blocks) for q in block}
        require(labels[0] == 0, "Quotient initial state order changed")
        return Machine(
            [tuple(labels[t] for t in self.transitions[block[0]]) for block in blocks],
            [self.outputs[block[0]] for block in blocks],
        ), labels


def first_distinguishing_word(left, right):
    """Independent exact product exploration; no length bound is assumed."""
    queue = deque([(0, 0, "")])
    seen = {(0, 0)}
    while queue:
        p, q, word = queue.popleft()
        if left.outputs[p] != right.outputs[q]:
            return word
        for i, letter in enumerate(ALPHABET):
            successor = (left.transitions[p][i], right.transitions[q][i])
            if successor not in seen:
                seen.add(successor)
                queue.append((*successor, word + letter))
    return None


def all_labelled_machines(n):
    for flat in product(range(n), repeat=n * len(ALPHABET)):
        transitions = [flat[2 * i:2 * i + 2] for i in range(n)]
        for outputs in product((0, 1), repeat=n):
            yield Machine(transitions, outputs)


def check_small_length_bounds():
    machines = {n: tuple(all_labelled_machines(n)) for n in (1, 2)}
    rows = []
    for r, s in ((1, 1), (1, 2), (2, 2)):
        pairs = combinations(machines[r], 2) if r == s else product(machines[r], machines[s])
        total = distinct = 0
        maximum = -1
        witness = None
        for left, right in pairs:
            total += 1
            word = first_distinguishing_word(left, right)
            if word is None:
                continue
            distinct += 1
            require(len(word) <= r + s - 2, "Proposed distinguishing bound fails")
            if len(word) > maximum:
                maximum = len(word)
                witness = {
                    "word": word,
                    "left_transitions": left.transitions,
                    "left_outputs": left.outputs,
                    "right_transitions": right.transitions,
                    "right_outputs": right.outputs,
                }
        rows.append({
            "left_state_count": r,
            "right_state_count": s,
            "machine_pairs_checked": total,
            "behaviorally_distinct_pairs": distinct,
            "maximum_shortest_distinguishing_length": maximum,
            "proposed_bound": r + s - 2,
            "maximum_witness": witness,
        })
    return rows


def check_length_bound_sharpness():
    results = []
    for n in range(2, 21):
        a_transitions = tuple((q + 1) % n for q in range(n))
        b_transitions = tuple(q + 1 if q < n - 1 else 1 for q in range(n))
        outputs = tuple(int(q == n - 1) for q in range(n))
        # The machine helper has two input columns. Duplicating the unary
        # transition makes its minimization identical to unary minimization.
        left = Machine([(q, q) for q in a_transitions], outputs)
        right = Machine([(q, q) for q in b_transitions], outputs)
        require(len(left.partition()) == n and len(right.partition()) == n, "Sharpness machine is not minimal")
        require(len(set(a_transitions)) == n, "Cycle generator is not bijective")
        require(len(set(b_transitions)) == n - 1 and b_transitions[0] == b_transitions[n - 1] == 1, "Tail-cycle generator does not exhibit the claimed collapse")
        word = first_distinguishing_word(left, right)
        require(word == "a" * (2 * n - 2), "Sharpness family has wrong first distinguishing length")
        require(all(left.output("a" * k) == right.output("a" * k) for k in range(2 * n - 2)), "Sharpness machines differ too early")
        require([left.output(word), right.output(word)] == [0, 1], "Sharpness witness has wrong outputs")
        results.append({
            "states_in_each_machine": n,
            "minimal_states_in_each_machine": n,
            "first_distinguishing_length": len(word),
            "left_and_right_outputs": [left.output(word), right.output(word)],
            "left_generator_is_bijective": True,
            "right_generator_is_bijective": False,
        })
    return {
        "effective_alphabet": ["a"],
        "family": "A: i -> i+1 mod N; B: i -> i+1 below N-1, N-1 -> 1; initial 0; sole accepting state N-1",
        "checked_instances": results,
        "scope": "N=2 through N=20 only; the general sharpness claim requires the accompanying proof",
    }


def check_s3():
    states = tuple(phi(word) for word in H)
    require(len(set(states)) == 6 and set(states) == set(permutations(range(3))), "H is not a full S3 cover")
    name = dict(zip(states, H))
    transitions = tuple(tuple(states.index(compose(g, GENERATORS[a])) for a in ALPHABET) for g in states)
    machine = Machine(transitions, [int(g == IDENTITY) for g in states])
    require(len(machine.partition()) == 6, "S3 machine is not minimal")
    require(behavior("abab") == 1 and behavior("baab") == 0, "Concrete noncommutativity observation failed")

    quotient_results = []
    blocks_by_depth = []
    labels_by_depth = []
    for k in range(4):
        suffixes = words_through(k)
        signature = lambda g: tuple(int(compose(g, phi(v)) == IDENTITY) for v in suffixes)
        blocks = partition_by_signatures(states, signature)
        blocks_by_depth.append(blocks)
        labels_by_depth.append({g: i for i, block in enumerate(blocks) for g in block})
    require([len(b) for b in blocks_by_depth] == [2, 4, 6, 6], "Unexpected finite-depth quotient sizes")
    for k in range(3):
        blocks = blocks_by_depth[k]
        labels = labels_by_depth[k]
        next_labels = labels_by_depth[k + 1]
        letter_results = {}
        for letter in ALPHABET:
            counterexample = None
            for block in blocks:
                for g, h in combinations(block, 2):
                    gs, hs = compose(g, GENERATORS[letter]), compose(h, GENERATORS[letter])
                    if labels[gs] != labels[hs]:
                        suffix = next(v for v in words_through(k) if int(compose(gs, phi(v)) == IDENTITY) != int(compose(hs, phi(v)) == IDENTITY))
                        counterexample = {
                            "same_class_histories": [name[g], name[h]],
                            "letter": letter,
                            "distinguishing_suffix_after_letter": suffix,
                            "resulting_query_words": [name[g] + letter + suffix, name[h] + letter + suffix],
                            "responses": [behavior(name[g] + letter + suffix), behavior(name[h] + letter + suffix)],
                        }
                        break
                if counterexample:
                    break
            # The inter-level map Q_(k+1) -> Q_k must exist even if the
            # same-level map Q_k -> Q_k does not.
            restriction = {}
            typed_transition = {}
            for g in states:
                source = next_labels[g]
                destination = labels[compose(g, GENERATORS[letter])]
                require(source not in restriction or restriction[source] == labels[g], "Restriction map ill-defined")
                require(source not in typed_transition or typed_transition[source] == destination, "Typed transition ill-defined")
                restriction[source] = labels[g]
                typed_transition[source] = destination
            fiber_constant = all(
                restriction[x] != restriction[y] or typed_transition[x] == typed_transition[y]
                for x in restriction for y in restriction
            )
            require(fiber_constant == (counterexample is None), "Kernel-fiber descent criterion differs from direct criterion")
            letter_results[letter] = {
                "same_level_transition_descends": counterexample is None,
                "failure_witness": counterexample,
                "interlevel_transition_well_defined": True,
                "interlevel_map_constant_on_restriction_fibers": fiber_constant,
            }
        require(all(item["same_level_transition_descends"] for item in letter_results.values()) == (k == 2), "Unexpected descent stage")
        quotient_results.append({
            "depth": k,
            "class_count": len(blocks),
            "classes_as_H_representatives": [[name[g] for g in block] for block in blocks],
            "letters": letter_results,
        })

    prefix_cover = set(H) | {h + a for h in H for a in ALPHABET}
    tests = sorted({p + v for p in prefix_cover for v in H}, key=word_key)
    rows = {p: tuple(behavior(p + v) for v in H) for p in prefix_cover}
    require(len({rows[h] for h in H}) == 6, "Certificate does not distinguish six states")
    require(all(sum(rows[h]) == 1 for h in H), "Group rows not permutation indicator rows")
    row_names = {rows[h]: h for h in H}
    successors = {h: {a: row_names[rows[h + a]] for a in ALPHABET} for h in H}
    require(all(phi(successors[h][a]) == phi(h + a) for h in H for a in ALPHABET), "Table reconstruction gives wrong successor")
    require(max(map(len, tests)) == 5 and len(tests) == 48, "Unexpected conformance certificate size")
    require(len(words_through(10)) == 2047, "Wrong exhaustive query count")

    # Generate the finite transition monoid, using apply-left-then-right.
    identity = tuple(range(6))
    letter_maps = [tuple(row[i] for row in transitions) for i in range(2)]
    monoid = {identity}
    queue = deque([identity])
    while queue:
        transform = queue.popleft()
        for generator in letter_maps:
            composed = tuple(generator[transform[i]] for i in range(6))
            if composed not in monoid:
                monoid.add(composed)
                queue.append(composed)
    require(len(monoid) == 6 and all(len(set(t)) == 6 for t in monoid), "Transition monoid is not a six-element group")
    require(tuple(letter_maps[1][letter_maps[0][i]] for i in range(6)) != tuple(letter_maps[0][letter_maps[1][i]] for i in range(6)), "Generator actions commute")

    return {
        "permutation_convention": "(p*q)(i) = p(q(i)); state update g -> g*phi(letter); phi(uv)=phi(u)*phi(v)",
        "empty_word_encoding": "",
        "H": list(H),
        "H_permutations_zero_based": states,
        "finite_depth_quotients": quotient_results,
        "certificate": {
            "prefix_cover_size": len(prefix_cover),
            "query_count": len(tests),
            "maximum_query_length": max(map(len, tests)),
            "query_counts_by_length": dict(sorted(Counter(map(len, tests)).items())),
            "queries": tests,
            "H_rows_in_H_column_order": {h: rows[h] for h in H},
            "reconstructed_successors_in_H": successors,
            "exhaustive_length_10_query_count": len(words_through(10)),
            "model_promise": "At most six reachable observationally distinguishable states; not inferred by these finite checks",
        },
        "transition_monoid_size": len(monoid),
        "all_transition_maps_bijective": True,
        "generator_maps_noncommuting": True,
        "concrete_word_observations": {"abab": behavior("abab"), "baab": behavior("baab")},
    }


def truncated_machine(horizon):
    # Only reachable states are included; None is the absorbing rejecting state.
    states = [(0, IDENTITY)]
    index = {states[0]: 0}
    transitions = []
    outputs = []
    cursor = 0
    while cursor < len(states):
        current = states[cursor]
        row = []
        outputs.append(int(current is not None and current[1] == IDENTITY))
        for letter in ALPHABET:
            if current is None or current[0] == horizon:
                successor = None
            else:
                successor = (current[0] + 1, compose(current[1], GENERATORS[letter]))
            if successor not in index:
                index[successor] = len(states)
                states.append(successor)
            row.append(index[successor])
        transitions.append(row)
        cursor += 1
    return Machine(transitions, outputs), index[None]


def check_delayed_failures():
    rows = []
    for horizon in range(7):
        raw, sink = truncated_machine(horizon)
        minimal, quotient = raw.minimal_quotient()
        min_sink = quotient[sink]
        tests = words_through(horizon)
        require(all(raw.output(w) == behavior(w) for w in tests), "Truncation disagrees before horizon")
        require(all(minimal.output(w) == raw.output(w) for w in words_through(horizon + 2)), "Minimization changed response")
        reset_word = "a" * (horizon + 1)
        image = {minimal.after(reset_word, state=q) for q in range(minimal.n)}
        require(image == {min_sink}, "Long word is not constant on minimal states")
        require(minimal.n >= 2 and minimal.outputs[0] == 1 and minimal.outputs[min_sink] == 0, "Nonbijectivity witness collapsed")
        distinction = "a" * (2 * ((horizon // 2) + 1))
        require(len(distinction) > horizon and behavior(distinction) == 1 and minimal.output(distinction) == 0, "No beyond-horizon distinction")
        rows.append({
            "horizon": horizon,
            "all_words_through_horizon_checked": len(tests),
            "reachable_raw_states": raw.n,
            "minimal_states": minimal.n,
            "constant_transformation_word": reset_word,
            "constant_transformation_image_size": len(image),
            "beyond_horizon_distinguishing_word": distinction,
            "original_and_truncated_responses": [behavior(distinction), minimal.output(distinction)],
            "syntactic_monoid_is_not_a_group": True,
        })
    return rows


def run():
    return {
        "s3": check_s3(),
        "delayed_irreversible_completions": check_delayed_failures(),
        "small_exhaustive_distinguishing_length_checks": check_small_length_bounds(),
        "distinguishing_length_sharpness_family": check_length_bound_sharpness(),
    }
