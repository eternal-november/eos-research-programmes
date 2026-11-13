"""Exact checks for threshold observations of an unknown finite transition."""

from collections import Counter
from itertools import combinations, product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


class Oracle:
    def __init__(self, values):
        self.values = tuple(values)
        self.n = len(values)
        self.log = []

    def query(self, i, j):
        # Rows are zero-based here; threshold labels are the paper's 2,...,n.
        require(0 <= i < self.n and 2 <= j <= self.n, "Illegal primitive query")
        answer = int(self.values[i] >= j)
        require(all((i, j) != (r, s) for r, s, _ in self.log), "Repeated primitive query")
        self.log.append((i, j, answer))
        return answer

    def intervals(self):
        lower, upper = [1] * self.n, [self.n] * self.n
        for i, j, answer in self.log:
            if answer:
                lower[i] = max(lower[i], j)
            else:
                upper[i] = min(upper[i], j - 1)
        return tuple(zip(lower, upper))


def monotone(values):
    return all(x <= y for x, y in zip(values, values[1:]))


def all_completions_monotone(intervals):
    return all(intervals[i][1] <= intervals[i + 1][0] for i in range(len(intervals) - 1))


def some_completion_monotone(intervals):
    return all(intervals[i][0] <= intervals[j][1] for i in range(len(intervals)) for j in range(i + 1, len(intervals)))


def adaptive_test(oracle):
    value = 1
    recovered = []
    for i in range(oracle.n):
        if i > 0 and value > 1 and oracle.query(i, value) == 0:
            return False, recovered, (i - 1, i, value)
        while value < oracle.n:
            if oracle.query(i, value + 1):
                value += 1
            else:
                break
        recovered.append(value)
    return True, recovered, None


def independent_binary_recovery(oracle):
    values = []
    for i in range(oracle.n):
        lower, upper = 1, oracle.n
        while lower < upper:
            threshold = (lower + upper + 1) // 2
            if oracle.query(i, threshold):
                lower = threshold
            else:
                upper = threshold - 1
        values.append(lower)
    return tuple(values)


def check_all_functions():
    results = []
    for n in range(1, 7):
        histogram = Counter()
        positive_histogram = Counter()
        negative_histogram = Counter()
        maximum = maximum_binary = -1
        maximum_example = maximum_log = None
        positive_count = negative_count = nonempty_preserving_count = 0
        for values in product(range(1, n + 1), repeat=n):
            oracle = Oracle(values)
            passed, recovered, witness = adaptive_test(oracle)
            require(passed == monotone(values), "Adaptive tester classification fails")
            require(tuple(recovered) == values[:len(recovered)], "Completed row value is inexact")
            require(len(oracle.log) <= 3 * n - 2, "Claimed primitive-query bound fails")
            intervals = oracle.intervals()
            if passed:
                positive_count += 1
                positive_histogram[len(oracle.log)] += 1
                require(all_completions_monotone(intervals), "Positive transcript is not a universal certificate")
                require(all(lo == hi == value for (lo, hi), value in zip(intervals, values)), "Positive run did not exactly recover every row")
            else:
                negative_count += 1
                negative_histogram[len(oracle.log)] += 1
                left, right, threshold = witness
                require(values[left] >= threshold > values[right], "Inversion witness is false")
                require(intervals[left][0] > intervals[right][1], "Witness not forced by acquired observations")
                require(not some_completion_monotone(intervals), "Negative transcript admits a monotone completion")

            # Directly test every preimage of an old threshold support.
            tail_supports = {tuple(i >= j for i in range(1, n + 1)) for j in range(1, n + 2)}
            preimages = [tuple(value >= j for value in values) for j in range(1, n + 2)]
            require(all(support in tail_supports for support in preimages) == passed, "Incidence preimage-closure differs from monotonicity")
            nonempty_tails = tail_supports - {(False,) * n}
            preserves_nonempty = all(support in nonempty_tails for support in preimages[:-1])
            require(preserves_nonempty == (passed and values[-1] == n), "Absent-empty-support variant has wrong criterion")
            nonempty_preserving_count += preserves_nonempty
            binary = Oracle(values)
            require(independent_binary_recovery(binary) == values, "Independent binary recovery fails")
            maximum_binary = max(maximum_binary, len(binary.log))
            histogram[len(oracle.log)] += 1
            if len(oracle.log) > maximum:
                maximum = len(oracle.log)
                maximum_example, maximum_log = values, oracle.log
        results.append({
            "n": n,
            "functions_checked": n ** n,
            "monotone_functions": positive_count,
            "nonmonotone_functions": negative_count,
            "functions_preserving_tails_when_empty_support_is_omitted": nonempty_preserving_count,
            "adaptive_query_histogram": dict(sorted(histogram.items())),
            "positive_query_histogram": dict(sorted(positive_histogram.items())),
            "negative_query_histogram": dict(sorted(negative_histogram.items())),
            "maximum_adaptive_queries": maximum,
            "maximum_example": maximum_example,
            "maximum_example_primitive_log_zero_based_rows": maximum_log,
            "maximum_independent_binary_recovery_queries": maximum_binary,
            "full_additional_threshold_table_queries": n * (n - 1),
            "claimed_upper_bound": 3 * n - 2,
        })
    require([row["maximum_adaptive_queries"] for row in results] == [0, 2, 6, 9, 12, 15], "Unexpected exact adaptive maxima")
    return results


def check_empty_support_regression():
    results = []
    for n in range(2, 7):
        values = (1,) * n
        preimage_of_second_tail = tuple(value >= 2 for value in values)
        require(monotone(values) and not any(preimage_of_second_tail), "Constant-one regression is wrong")
        results.append({
            "n": n, "transition_values": values, "transition_is_monotone": True,
            "preimage_of_threshold_2_is_empty": True,
            "empty_support_generated_by_intersections_of_nonempty_tails": False,
            "nonempty_tail_closure_preserved": False,
        })
    return {
        "required_old_test_family": "Thresholds j=1,...,n+1; j=n+1 is the explicitly supplied constant-false test",
        "if_constant_false_is_omitted": "Preimage closure requires monotonicity AND delta(n)=n",
        "counterexamples": results,
    }


def check_interval_criteria():
    results = []
    for n in range(1, 5):
        intervals = tuple((lo, hi) for lo in range(1, n + 1) for hi in range(lo, n + 1))
        tables = comparisons = universal = possible = 0
        for table in product(intervals, repeat=n):
            completions = tuple(product(*(range(lo, hi + 1) for lo, hi in table)))
            truth = [monotone(values) for values in completions]
            require(all(truth) == all_completions_monotone(table), "Universal interval criterion fails")
            require(any(truth) == some_completion_monotone(table), "Existential interval criterion fails")
            tables += 1
            comparisons += len(completions)
            universal += all(truth)
            possible += any(truth)
        results.append({
            "n": n,
            "interval_tables_checked": tables,
            "table_completion_pairs_checked": comparisons,
            "tables_forcing_monotonicity": universal,
            "tables_admitting_monotonicity": possible,
        })
    return results


def check_constant_certificates():
    results = []
    for n in (3, 4):
        query_positions = tuple(product(range(n), range(2, n + 1)))
        for c in range(2, n):
            minimum = len(query_positions) + 1
            minimum_log = None
            certificates = 0
            for mask in range(1 << len(query_positions)):
                oracle = Oracle((c,) * n)
                for bit, (i, j) in enumerate(query_positions):
                    if mask & (1 << bit):
                        oracle.query(i, j)
                if all_completions_monotone(oracle.intervals()):
                    certificates += 1
                    if len(oracle.log) < minimum:
                        minimum, minimum_log = len(oracle.log), oracle.log
            require(minimum == 2 * n - 2, "Interior-constant certificate lower bound fails")
            # Construct each necessary-query adversary independently. Omitting
            # q(i,c+1) for i<n permits raising that value; omitting q(i,c)
            # for i>1 permits lowering it. They preserve all other answers.
            adversaries = []
            for i, threshold, changed in [
                *((i, c + 1, c + 1) for i in range(n - 1)),
                *((i, c, c - 1) for i in range(1, n)),
            ]:
                values = [c] * n
                values[i] = changed
                require(not monotone(values), "Missing-query adversary remains monotone")
                differing = [(r, j) for r, j in query_positions if int(values[r] >= j) != int(c >= j)]
                require(differing == [(i, threshold)], "Adversary changes more than the missing query")
                adversaries.append({"omitted_query": [i, threshold], "alternative": values})
            results.append({
                "n": n,
                "constant_value": c,
                "query_subsets_enumerated": 1 << len(query_positions),
                "certifying_subsets": certificates,
                "minimum_primitive_queries": minimum,
                "minimum_certificate_log_zero_based_rows": minimum_log,
                "necessary_query_adversaries": adversaries,
            })
    return results


def positive_ambiguity_transcript(oracle, k):
    require(oracle.n == 2 * k, "Wrong size for positive ambiguity family")
    for i in range(k):
        if i > 0:
            require(oracle.query(i, 2 * i + 1) == 1, "Expected lower-bound response failed")
        if i < k - 1:
            require(oracle.query(i, 2 * i + 3) == 0, "Expected upper-bound response failed")
    for i in range(k, 2 * k):
        require(oracle.query(i, 2 * k) == 1, "Expected terminal constant response failed")


def check_positive_ambiguity_family():
    results = []
    for k in range(1, 9):
        n = 2 * k
        actual = tuple(2 * i + 1 for i in range(k)) + (n,) * k
        oracle = Oracle(actual)
        positive_ambiguity_transcript(oracle, k)
        transcript = list(oracle.log)
        require(len(transcript) == 3 * k - 2, "Positive ambiguity transcript has wrong query cost")
        intervals = oracle.intervals()
        require(intervals == tuple((2 * i + 1, 2 * i + 2) for i in range(k)) + ((n, n),) * k, "Positive ambiguity intervals are wrong")
        completions = tuple(product(*(range(lo, hi + 1) for lo, hi in intervals)))
        require(len(completions) == 2 ** k and all(monotone(v) for v in completions), "Positive transcript does not leave exactly 2^k monotone transitions")
        require(all_completions_monotone(intervals), "Positive ambiguity transcript is not a universal certificate")
        bit_vectors = set()
        for candidate in completions:
            candidate_oracle = Oracle(candidate)
            positive_ambiguity_transcript(candidate_oracle, k)
            require(candidate_oracle.log == transcript, "A compatible transition gives different acquired answers")
            bits = tuple(candidate_oracle.query(i, 2 * i + 2) for i in range(k))
            bit_vectors.add(bits)
            require(candidate_oracle.intervals() == tuple((v, v) for v in candidate), "The k resolving queries fail to identify the transition")
            require(len(candidate_oracle.log) - len(transcript) == k, "Resolving stage has wrong cost")
        require(len(bit_vectors) == 2 ** k, "Resolving bits do not distinguish all remaining transitions")
        results.append({
            "k": k, "n": n, "initial_primitive_queries": len(transcript),
            "compatible_monotone_predictors": len(completions),
            "additional_resolving_queries": k,
            "intervals_after_positive_certificate": intervals,
            "initial_query_log_zero_based_rows": transcript,
        })
    return results


def run():
    return {
        "threshold_functions": check_all_functions(),
        "empty_support_prerequisite": check_empty_support_regression(),
        "partial_threshold_interval_criteria": check_interval_criteria(),
        "constant_function_certificate_lower_bound": check_constant_certificates(),
        "positive_certificate_with_predictor_ambiguity": check_positive_ambiguity_family(),
    }
