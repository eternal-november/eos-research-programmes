"""Exact finite diagnostics for recurrent D_fin + augmented-vector interaction.

Run with Python 3, without -O. Only stdlib is used; no files are written.
Finite checks supplement the written argument; they do not certify a general
categorical feedback theorem, the occurrence runtime, or a physical substrate.
The two implementations below are a step-kernel closure and an independent
direct fold over complete two-epoch raw choices. Neither calls the other.
"""

from collections import defaultdict
from dataclasses import dataclass, replace
from fractions import Fraction as F
from itertools import permutations, product
import json


MODES = ("diag", "anti", "independent")
BITS = tuple(product((0, 1), repeat=2))
SCHEDULES = tuple(s for s in permutations(("R1", "W1", "R2", "W2"))
                  if s.index("R1") < s.index("W1") and s.index("R2") < s.index("W2"))


def coupling(mode, b1, b2):
    if mode == "diag":
        return F(int(b1 == b2), 2)
    if mode == "anti":
        return F(int(b1 != b2), 2)
    assert mode == "independent"
    return F(1, 4)


def next_mode(completed_public_x):
    """The delayed controller consumes only the completed public counter."""
    return MODES[completed_public_x % 3]


def raw_draws(source):
    # Source coordinates: b1,b2,a1,a2. The two a_i are erased auxiliaries.
    # All outcomes are retained, even those with coupling weight zero.
    return tuple(product((0, 1), repeat=4 if source else 2))


def draw_weight(mode, draw, source):
    return coupling(mode, draw[0], draw[1]) / (4 if source else 1)


@dataclass(frozen=True)
class State:
    epoch: int
    stage: str
    x: int
    mode: str
    progress: tuple = (0, 0)
    reads: tuple = (None, None)
    bits: tuple = (None, None)
    aux: tuple | None = None


@dataclass(frozen=True)
class Prefix:
    states: tuple
    events: tuple = ()

    @property
    def state(self):
        return self.states[-1]

    def append(self, state, event):
        return Prefix(self.states + (state,), self.events + (event,))

    def truncate(self):
        assert self.events
        return Prefix(self.states[:-1], self.events[:-1])


def erase_state(state):
    return replace(state, aux=None)


def erase_prefix(prefix):
    events = tuple(event[:5] if event[0] == "draw" else event for event in prefix.events)
    return Prefix(tuple(erase_state(state) for state in prefix.states), events)


def writer_tag(event):
    # A single fixed writer grade Q is used by all microsteps. Detailed values
    # in events are retained boundary-history data, not changing writer grades.
    return ("sample", event[3], event[4]) if event[0] == "draw" else (event[0],)


WRITER_CARRIER = tuple(("sample", *bits) for bits in BITS) + tuple(
    (label,) for label in ("R1", "W1", "R2", "W2", "restart"))


def writer_coefficient_dimension(tag):
    assert tag in WRITER_CARRIER
    return 3 if tag[0] == "sample" else 1


def enabled(state):
    if state.stage == "draw":
        return ("draw",)
    if state.stage == "restart":
        return ("restart",)
    assert state.stage == "active"
    return tuple(("R" if progress == 0 else "W") + str(i + 1)
                 for i, progress in enumerate(state.progress) if progress < 2)


def public_scheduler_observation(state):
    # In particular, no auxiliary bits, unseen draw, or raw witness eliminator.
    return state.epoch, state.stage, state.progress


def scheduled_label(state, schedules):
    epoch, stage, progress = public_scheduler_observation(state)
    if stage == "draw":
        return "draw"
    if stage == "restart":
        return "restart"
    return schedules[epoch][sum(progress)]


def kernel_step(prefix, label, draw, source):
    """Primitive small step, acting on one shared counter and two registers."""
    state = prefix.state
    assert label in enabled(state)
    if label == "draw":
        assert draw in raw_draws(source)
        b1, b2 = draw[:2]
        aux = tuple(draw[2:]) if source else None
        after = replace(state, stage="active", bits=(b1, b2), aux=aux)
        event = ("draw", state.epoch, state.mode, b1, b2) + (() if aux is None else aux)
        return prefix.append(after, event), draw_weight(state.mode, draw, source)
    if label == "restart":
        mode = next_mode(state.x)
        after = State(state.epoch + 1, "draw", state.x, mode)
        return prefix.append(after, ("restart", state.epoch + 1, state.x, mode)), F(1)
    worker = int(label[1]) - 1
    progress = list(state.progress)
    reads = list(state.reads)
    if label[0] == "R":
        assert progress[worker] == 0
        reads[worker] = state.x
        progress[worker] = 1
        after = replace(state, progress=tuple(progress), reads=tuple(reads))
        event = (label, state.epoch, state.x)
    else:
        assert progress[worker] == 1
        progress[worker] = 2
        new_x = reads[worker] + 1 + state.bits[worker]
        after = replace(state, x=new_x, progress=tuple(progress),
                        stage="restart" if progress == [2, 2] else "active")
        event = (label, state.epoch, state.x, reads[worker], state.bits[worker], new_x)
    # The chosen joint draw and its actual coupling stay in state throughout
    # all four worker microsteps; there is no resampling of marginal bits.
    assert after.bits == state.bits and after.mode == state.mode and after.aux == state.aux
    return prefix.append(after, event), F(1)


def add(table, key, mass):
    # Deliberately retains keys with exactly zero mass.
    table[key] += mass


def closure(initial_mode, schedules, source):
    """Close the primitive kernel one microstep at a time, for 12 steps."""
    initial = Prefix((State(0, "draw", 0, initial_mode),))
    tables = [{initial: F(1)}]
    for _ in range(12):
        after = defaultdict(F)
        for prefix, mass in tables[-1].items():
            label = scheduled_label(prefix.state, schedules)
            choices = raw_draws(source) if label == "draw" else (None,)
            for draw in choices:
                new_prefix, weight = kernel_step(prefix, label, draw, source)
                add(after, new_prefix, mass * weight)
        tables.append(dict(after))
    return tables


def direct_fold(initial_mode, schedules, draws, source):
    """Independent chronological formulas; does not call kernel_step."""
    x = 0
    mode = initial_mode
    states = [State(0, "draw", x, mode)]
    events = []
    mass = F(1)
    for epoch, (schedule, draw) in enumerate(zip(schedules, draws)):
        b1, b2 = draw[:2]
        bits = (b1, b2)
        aux = tuple(draw[2:]) if source else None
        mass *= coupling(mode, b1, b2) / (4 if source else 1)
        progress = [0, 0]
        reads = [None, None]
        states.append(State(epoch, "active", x, mode, (0, 0), (None, None), bits, aux))
        events.append(("draw", epoch, mode, b1, b2) + (() if aux is None else aux))
        for label in schedule:
            worker = int(label[1]) - 1
            if label[0] == "R":
                assert progress[worker] == 0
                reads[worker] = x
                progress[worker] += 1
                events.append((label, epoch, x))
            else:
                assert progress[worker] == 1
                old_x = x
                x = reads[worker] + 1 + bits[worker]
                progress[worker] += 1
                events.append((label, epoch, old_x, reads[worker], bits[worker], x))
            stage = "restart" if progress == [2, 2] else "active"
            states.append(State(epoch, stage, x, mode, tuple(progress), tuple(reads), bits, aux))
        mode = MODES[x % 3]
        states.append(State(epoch + 1, "draw", x, mode))
        events.append(("restart", epoch + 1, x, mode))
    return Prefix(tuple(states), tuple(events)), mass


def direct_prefix_tables(initial_mode, schedules, source):
    tables = [defaultdict(F) for _ in range(13)]
    for draws in product(raw_draws(source), repeat=2):
        full, mass = direct_fold(initial_mode, schedules, draws, source)
        for length in range(13):
            prefix = Prefix(full.states[:length + 1], full.events[:length])
            add(tables[length], prefix, mass)
    return [dict(table) for table in tables]


def push(table, function):
    pushed = defaultdict(F)
    for key, mass in table.items():
        add(pushed, function(key), mass)
    return dict(pushed)


# Small exact linear algebra. Matrices are nonempty row tuples; all dimensions
# used here are at most 9, and no external numerical or symbolic package is used.
def mat(rows):
    result = tuple(tuple(F(value) for value in row) for row in rows)
    assert result and result[0] and len({len(row) for row in result}) == 1
    return result


def identity(size):
    return mat([[int(i == j) for j in range(size)] for i in range(size)])


def mm(left, right):
    assert len(left[0]) == len(right)
    return mat([[sum(left[i][k] * right[k][j] for k in range(len(right)))
                 for j in range(len(right[0]))] for i in range(len(left))])


def tensor(left, right):
    return mat([[left[i][j] * right[k][l]
                 for j in range(len(left[0])) for l in range(len(right[0]))]
                for i in range(len(left)) for k in range(len(right))])


def tensor_power(matrix, exponent):
    answer = identity(1)
    for _ in range(exponent):
        answer = tensor(answer, matrix)
    return answer


def rank(matrix):
    rows = [list(row) for row in matrix]
    pivot = 0
    for column in range(len(rows[0])):
        found = next((i for i in range(pivot, len(rows)) if rows[i][column]), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        denominator = rows[pivot][column]
        rows[pivot] = [x / denominator for x in rows[pivot]]
        for i in range(len(rows)):
            if i != pivot:
                factor = rows[i][column]
                rows[i] = [x - factor * y for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def json_matrix(matrix):
    return [[int(value) if value.denominator == 1 else str(value) for value in row]
            for row in matrix]


def grade_checks():
    eps_u = mat([[1, 0]])
    eps_p = mat([[1, 0, 0]])
    projection = mat([[1, 0], [0, 0]])
    embed = mat([[1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 0, 1]])
    primitive_pair = mat([[1, 0, 0, 0], [0, 1, 0, 0],
                          [0, 0, 1, 0], [0, 0, 0, 0]])
    alpha = mat([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
    assert mm(eps_u, projection) == eps_u
    assert mm(primitive_pair, embed) == mm(embed, alpha)
    assert mm(eps_p, alpha) == eps_p
    normalized = mat([[1], [0], [1]])
    assert mm(eps_p, normalized) == mat([[1]])
    assert mm(alpha, normalized) != normalized
    assert alpha != identity(3) and rank(alpha) == 2
    assert mm(alpha, alpha) == alpha

    # Prefix n contains ceil(n/6) draws. All other step coefficients are I=Q.
    # The same equations apply to context and content, whose coefficient
    # categories and arrows are retained separately. Repeating these matrix
    # equations under a second label would not be independent evidence.
    checked = 0
    for length in range(1, 13):
        old_count = (length - 1 + 5) // 6
        new_count = (length + 5) // 6
        old_alpha = tensor_power(alpha, old_count)
        new_alpha = tensor_power(alpha, new_count)
        if new_count == old_count:
            discard = identity(3 ** old_count)
        else:
            discard = tensor(identity(3 ** old_count), eps_p)
        assert mm(discard, new_alpha) == mm(old_alpha, discard)
        old_eps = tensor_power(eps_p, old_count)
        new_eps = tensor_power(eps_p, new_count)
        assert mm(old_eps, discard) == new_eps
        assert mm(new_eps, new_alpha) == new_eps
        checked += 1
    alpha_two = tensor(alpha, alpha)
    assert len(alpha_two) == 9 and rank(alpha_two) == 4

    # Arbitrary monoidal coefficient inputs do not themselves supply discards.
    # In (FinSet,+,empty), there are no functions from singleton to the unit.
    maps_nonempty_to_empty = 0 ** 1
    assert maps_nonempty_to_empty == 0
    # In Vect, a chosen functional need not be natural for unrestricted maps.
    swap = mat([[0, 1], [1, 0]])
    assert mm(eps_u, swap) != eps_u
    return {
        "joint_coefficient": "P = U x_Q U, U=(Q^2,pr1), coordinates (a,u,v)",
        "joint_embedding": json_matrix(embed),
        "actual_joint_native_map": json_matrix(alpha),
        "distinct_same_raw_maps": "identity_P and alpha_P; separated by normalized vector (1,0,1)",
        "one_draw_dimension_and_rank": [3, rank(alpha)],
        "two_draw_dimension_and_rank": [9, rank(alpha_two)],
        "prefix_matrix_squares_shared_by_context_and_content_formulas": checked,
        "fixed_writer_grade": "Q=(O,D_o); O has four sample(bitpair) tags and R1,W1,R2,W2,restart; D_sample=P, all other D_o=I=(rationals,id).",
        "native_writer_map": "Underlying id_O; beta_sample=alpha_P and beta_other=id_I. No unreachable part of Q^n is enumerated.",
        "truncation_formula": "id_(P^tensor n) tensor epsilon_P when the discarded step is a draw; identity otherwise",
        "discard_boundaries": {
            "FinSet_coproduct_unit": "No map singleton -> empty: affine effects do not imply grade discard.",
            "unrestricted_Vect": "pr1 composed with swap differs from pr1: selected discards require native naturality.",
        },
    }


def local_coupling_checks():
    for mode in MODES:
        q = {bits: coupling(mode, *bits) for bits in BITS}
        assert sum(q.values()) == 1
        for component in (0, 1):
            assert {bit: sum(weight for bits, weight in q.items() if bits[component] == bit)
                    for bit in (0, 1)} == {0: F(1, 2), 1: F(1, 2)}
        source = {draw: draw_weight(mode, draw, True) for draw in raw_draws(True)}
        assert push(source, lambda draw: draw[:2]) == q
        for component in (0, 1):
            marginal = push(source, lambda draw: (draw[component], draw[component + 2]))
            assert marginal == {pair: F(1, 4) for pair in BITS}
    assert {coupling("diag", *bits) for bits in BITS} == {F(0), F(1, 2)}
    assert any(coupling("diag", *bits) != coupling("anti", *bits) for bits in BITS)
    return {
        "retained_choices": list(MODES),
        "component_raw_sizes_source_target": [4, 2],
        "joint_raw_sizes_source_target": [16, 4],
        "joint_pushforward_and_component_marginals": True,
        "zero_weight_raw_outcomes_retained": True,
    }


def serial_and_interference_checks():
    serial = ("R1", "W1", "R2", "W2")
    overlap = ("R1", "R2", "W1", "W2")
    laws = {}
    for mode in MODES:
        law = defaultdict(F)
        for bits in BITS:
            prefix, _ = direct_fold(mode, (serial,), (bits,), False)
            add(law, prefix.state.x, coupling(mode, *bits))
        laws[mode] = dict(law)
    assert laws["diag"] == {2: F(1, 2), 3: F(0), 4: F(1, 2)}
    assert laws["anti"] == {2: F(0), 3: F(1), 4: F(0)}
    assert laws["independent"] == {2: F(1, 4), 3: F(1, 2), 4: F(1, 4)}
    lost = []
    for schedule in SCHEDULES:
        prefix, _ = direct_fold("diag", (schedule,), ((0, 0),), False)
        if prefix.state.x == 1:
            lost.append(" ".join(schedule))
        else:
            assert prefix.state.x == 2
    assert len(lost) == 4
    overlap_law = defaultdict(F)
    for bits in BITS:
        prefix, _ = direct_fold("independent", (overlap,), (bits,), False)
        add(overlap_law, prefix.state.x, coupling("independent", *bits))
    assert dict(overlap_law) == {1: F(1, 2), 2: F(1, 2)}

    # Shared closure updates the state before the second component reads it.
    shared_x = 0
    shared_x = 1 - shared_x
    shared_read = shared_x
    # Independent closure gives each component its own feedback state.
    left_x, right_x = 0, 0
    left_x = 1 - left_x
    independent_read = right_x
    assert shared_read == 1 and independent_read == 0
    assert left_x != right_x  # They do not form an agreeing shared-state cone.
    return {
        "serial_increment_laws": {mode: {str(x): str(p) for x, p in law.items()}
                                  for mode, law in laws.items()},
        "lost_update_schedules_at_bits_00": lost,
        "overlap_independent_final_law": {str(x): str(p) for x, p in overlap_law.items()},
        "independent_versus_shared_feedback": {
            "shared_flip_then_read": shared_read,
            "independently_closed_reader": independent_read,
            "independent_final_states_disagree": True,
        },
    }


def combined_checks():
    counts = defaultdict(int)
    modes_after_feedback = set()
    for initial_mode in MODES:
        for schedules in product(SCHEDULES, repeat=2):
            source = closure(initial_mode, schedules, True)
            target = closure(initial_mode, schedules, False)
            assert source == direct_prefix_tables(initial_mode, schedules, True)
            assert target == direct_prefix_tables(initial_mode, schedules, False)
            counts["closure_direct_fold_comparisons"] += 2
            for length in range(13):
                assert sum(source[length].values()) == sum(target[length].values()) == 1
                assert push(source[length], erase_prefix) == target[length]
                # This equality includes zero-mass keys, so checks raw coverage
                # separately from equality of positive-probability support.
                assert {erase_prefix(prefix) for prefix in source[length]} == set(target[length])
                counts["exact_prefix_law_comparisons"] += 1
                counts["source_raw_prefixes"] += len(source[length])
                counts["target_raw_prefixes"] += len(target[length])
                for prefix in source[length]:
                    image = erase_prefix(prefix)
                    assert enabled(prefix.state) == enabled(image.state)
                    assert public_scheduler_observation(prefix.state) == public_scheduler_observation(image.state)
                    context_dimension = 3 ** sum(event[0] == "draw" for event in prefix.events)
                    content_dimension = 1
                    for event, target_event in zip(prefix.events, image.events):
                        tag = writer_tag(event)
                        assert tag == writer_tag(target_event)
                        content_dimension *= writer_coefficient_dimension(tag)
                    assert content_dimension == context_dimension == 3 ** ((length + 5) // 6)
                    if length < 12:
                        label = scheduled_label(prefix.state, schedules)
                        assert label in enabled(prefix.state)
                        assert label == scheduled_label(image.state, schedules)
                    if length:
                        assert erase_prefix(prefix.truncate()) == image.truncate()
                if length:
                    assert push(source[length], lambda prefix: prefix.truncate()) == source[length - 1]
                    assert push(target[length], lambda prefix: prefix.truncate()) == target[length - 1]
                    counts["effect_truncation_squares"] += 2
            for prefix, mass in source[-1].items():
                assert len(prefix.events) == 12
                assert prefix.states[6].x >= 1 and prefix.states[12].x >= 2
                assert prefix.states[6].mode == next_mode(prefix.states[6].x)
                assert prefix.states[12].mode == next_mode(prefix.states[12].x)
                assert prefix.events[6][2] == prefix.states[6].mode
                # At all actual boundaries the one source-to-target map is
                # used, rather than a separately selected finite-horizon lift.
                assert all(state.epoch == i // 6 for i, state in enumerate(prefix.states))
                if mass:
                    modes_after_feedback.add(prefix.states[6].mode)
                counts["source_raw_complete_paths"] += 1
                counts["source_zero_weight_complete_paths"] += int(mass == 0)
            counts["target_raw_complete_paths"] += len(target[-1])
            counts["families"] += 1
    assert counts["families"] == 3 * 6 * 6 == 108
    assert counts["source_raw_complete_paths"] == 108 * 16 * 16
    assert counts["target_raw_complete_paths"] == 108 * 4 * 4
    assert modes_after_feedback == set(MODES)
    return {
        **dict(counts),
        "horizon_microsteps": 12,
        "source_aux_erasure": "(b1,b2,a1,a2) -> (b1,b2), dropping only stored auxiliary state and auxiliary draw labels",
        "feedback_policy": "next q = (diag,anti,independent)[completed_public_x mod 3]",
        "positive_mass_next_modes_exercised": sorted(modes_after_feedback),
        "joint_choice_retained_through_four_microsteps": True,
        "all_enabled_menus_and_scheduler_information_checked": True,
        "bounded_progress_checks": "Each tested round takes 6 steps and increases its completed counter by at least 1, including zero-weight paths.",
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without optimization; assertions perform the diagnostics.")
    assert len(SCHEDULES) == 6
    result = {
        "status": "PASS",
        "model": "One shared counter, retained conditional finite probability laws, and independent context/content AugVect native coefficients.",
        "local_couplings": local_coupling_checks(),
        "native_coefficients": grade_checks(),
        "separating_behaviors": serial_and_interference_checks(),
        "combined_recurrent_comparison": combined_checks(),
        "scope": "Exact finite diagnostics at two epochs; not a general proof, an occurrence-machine interpretation bridge, a completed infinite D_fin effect, or physical-time/resource certification.",
        "unbounded_argument_boundary": "The written induction uses the no-idle rule menu: draw, four strictly advancing worker actions, restart. No scheduler fairness or elapsed-time conclusion is silently added. Infinite probability/grade completion is separate from these bounded checks.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
