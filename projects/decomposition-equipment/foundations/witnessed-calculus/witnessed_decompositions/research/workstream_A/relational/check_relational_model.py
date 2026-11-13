#!/usr/bin/env python3
"""Independent finite relational A2 certificate. Standard library only.

The uniform theorem is RelationalTargetProof.md, not this bounded enumeration.
Run from any directory; --output selects the JSON report. No external writes.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from pathlib import Path as FilePath
import hashlib
import json
import platform
import time

VALUES = (0, 1)

def bit_tuple(n, i):
    return tuple((i >> (n - 1 - j)) & 1 for j in range(n))

def tuple_int(xs):
    v = 0
    for x in xs:
        v = 2 * v + x
    return v

@lru_cache(None)
def table(n, mask):
    return tuple((bit_tuple(n, row >> 1), row & 1)
                 for row in range(1 << (n + 1)) if (mask >> row) & 1)

@lru_cache(None)
def join_mask(n, outer, children):
    """Implementation 1: relational natural join, then existential projection.

    Children are (arity, mask); enumerate rows, never existential truth values.
    """
    assert len(children) == n
    m = sum(a for a, _ in children)
    result = 0
    for mid, z in table(n, outer):
        choices = [tuple(xs for xs, y in table(a, b) if y == mid[i])
                   for i, (a, b) in enumerate(children)]
        for local_inputs in product(*choices):
            flat = tuple(x for xs in local_inputs for x in xs)
            result |= 1 << (2 * tuple_int(flat) + z)
    return m, result


def truth_mask(n, outer, children):
    """Implementation 2: enumerate candidate flattened inputs/outputs/witnesses.

    No use of table(), join_mask(), or row-join construction.
    """
    m = sum(a for a, _ in children)
    result = 0
    for external in range(1 << m):
        for z in VALUES:
            for intermediate in range(1 << n):
                if not ((outer >> (2 * intermediate + z)) & 1):
                    continue
                cursor = m
                good = True
                for i, (arity, mask) in enumerate(children):
                    cursor -= arity
                    local = (external >> cursor) & ((1 << arity) - 1)
                    y = (intermediate >> (n - 1 - i)) & 1
                    if not ((mask >> (2 * local + y)) & 1):
                        good = False
                        break
                if good:
                    result |= 1 << (2 * external + z)
                    break
    return m, result


@dataclass(frozen=True)
class Component:
    source: str
    target: str
    name: str

@dataclass(frozen=True)
class Profile:
    source: str
    target: str
    components: tuple[Component, ...]

    def __post_init__(self):
        current = self.source
        for i, c in enumerate(self.components):
            if c.source != current:
                raise ValueError(f"noncomposable slot {i}: expected source {current}, got {c.source}")
            current = c.target
        if current != self.target:
            raise ValueError(f"profile ends at {current}, not {self.target}; empty profile must be a loop")

@dataclass(frozen=True)
class Relation:
    output: Component
    profile: Profile
    mask: int

    def __post_init__(self):
        if (self.profile.source, self.profile.target) != (self.output.source, self.output.target):
            raise ValueError("relation output endpoints disagree with the complete input profile")
        if not (0 <= self.mask < (1 << (1 << (len(self.profile.components) + 1)))):
            raise ValueError("relation mask has rows outside its typed Bool domain")

    def outcomes(self, xs):
        if len(xs) != len(self.profile.components) or any(x not in VALUES for x in xs):
            raise ValueError("wrong relation input tuple")
        row = 2 * tuple_int(xs)
        return [z for z in VALUES if (self.mask >> (row + z)) & 1]


def relation(output, inputs, predicate):
    mask = sum(1 << (2 * i + z)
               for i in range(1 << len(inputs)) for z in VALUES
               if predicate(bit_tuple(len(inputs), i), z))
    return Relation(output, Profile(output.source, output.target, tuple(inputs)), mask)


def identity(c):
    return relation(c, (c,), lambda xs, z: xs[0] == z)


def compose(outer, children, method=join_mask):
    children = tuple(children)
    if len(children) != len(outer.profile.components):
        raise ValueError("replacement family has the wrong number of occurrence positions")
    for i, (expected, child) in enumerate(zip(outer.profile.components, children)):
        if child.output != expected:
            raise ValueError(f"wrong output at occurrence {i}: expected {expected.name}, got {child.output.name}")
    profile = Profile(outer.output.source, outer.output.target,
                      tuple(c for child in children for c in child.profile.components))
    _, mask = method(len(children), outer.mask,
                     tuple((len(r.profile.components), r.mask) for r in children))
    return Relation(outer.output, profile, mask)


@dataclass(frozen=True)
class Generator:
    name: str
    output: Component
    profile: Profile

    def validate_image(self, image):
        if image.output != self.output:
            raise ValueError(f"{self.name}: assigned output {image.output.name}, expected {self.output.name}")
        if image.profile != self.profile:
            raise ValueError(f"{self.name}: assigned ordered full profile does not equal the declared profile")

@dataclass(frozen=True)
class Leaf:
    output: Component

    @property
    def profile(self):
        return Profile(self.output.source, self.output.target, (self.output,))

@dataclass(frozen=True)
class Node:
    generator: Generator
    children: tuple

    def __post_init__(self):
        if tuple(t.output for t in self.children) != self.generator.profile.components:
            raise ValueError("syntax node children do not match ordered primitive input components")

    @property
    def output(self):
        return self.generator.output

    @property
    def profile(self):
        return Profile(self.output.source, self.output.target,
                       tuple(c for t in self.children for c in t.profile.components))


def corolla(g):
    return Node(g, tuple(Leaf(c) for c in g.profile.components))


def graft(t, replacements):
    replacements = tuple(replacements)
    if tuple(s.output for s in replacements) != t.profile.components:
        raise ValueError("syntax graft replacements do not match frontier occurrences")
    it = iter(replacements)
    def go(t):
        if isinstance(t, Leaf):
            return next(it)
        return Node(t.generator, tuple(go(s) for s in t.children))
    result = go(t)
    assert next(it, None) is None
    return result


def syntax_extend(t, images):
    if isinstance(t, Leaf):
        return t
    t.generator.validate_image(images[t.generator.name])
    return graft(images[t.generator.name],
                 tuple(syntax_extend(s, images) for s in t.children))


def recursive_eval(t, assignment):
    if isinstance(t, Leaf):
        return identity(t.output)
    rel = assignment[t.generator.name]
    t.generator.validate_image(rel)
    return compose(rel, tuple(recursive_eval(s, assignment) for s in t.children))


def global_eval(t, assignment):
    """Independent tree oracle: one variable per edge occurrence, global constraints.

    Does not call compose, join_mask, truth_mask, or recursive_eval.
    """
    next_var = 0
    leaves = []
    constraints = []
    def compile_node(t):
        nonlocal next_var
        if isinstance(t, Leaf):
            result = next_var
            next_var += 1
            leaves.append(result)
            return result
        args = tuple(compile_node(s) for s in t.children)
        result = next_var
        next_var += 1
        rel = assignment[t.generator.name]
        t.generator.validate_image(rel)
        constraints.append((rel.mask, args, result))
        return result
    output = compile_node(t)
    internal = [i for i in range(next_var) if i not in leaves and i != output]
    mask = 0
    for xs in product(VALUES, repeat=len(leaves)):
        for z in VALUES:
            vals = dict(zip(leaves, xs))
            if output in vals and vals[output] != z:
                continue
            vals[output] = z
            for ys in product(VALUES, repeat=len(internal)):
                vals.update(zip(internal, ys))
                if all((rel >> (2 * tuple_int(tuple(vals[i] for i in args)) + vals[out])) & 1
                       for rel, args, out in constraints):
                    mask |= 1 << (2 * tuple_int(xs) + z)
                    break
    return Relation(t.output, t.profile, mask)


def describe_relation(r):
    return {"output": r.output.name, "profile": [c.name for c in r.profile.components],
            "mask": r.mask,
            "table": [{"inputs": list(xs), "outputs": r.outcomes(xs)}
                      for xs in product(VALUES, repeat=len(r.profile.components))]}


def expect_rejection(label, action):
    try:
        action()
    except ValueError as exc:
        return {"label": label, "rejected": True, "certificate": str(exc)}
    raise AssertionError(f"negative typing control {label} was silently accepted")


def finite_model():
    x = Component("a", "b", "x")
    r = Component("b", "b", "r")
    y = Component("b", "c", "y")
    tail = Component("b", "c", "tail")
    whole = Component("a", "c", "whole")
    def gen(name, out, ins):
        return Generator(name, out, Profile(out.source, out.target, tuple(ins)))
    gs = {
        "root": gen("root", whole, (x, tail)),
        "tail": gen("tail", tail, (r, y)),
        "fork": gen("fork", r, (r, r)),
        "red": gen("red", r, (r,)),
        "blue": gen("blue", r, (r,)),
        "erase": gen("erase", r, ()),
    }
    alpha = {
        "root": relation(whole, (x, tail), lambda v, z: z == (v[0] ^ v[1]) or v == (1, 1)),
        "tail": relation(tail, (r, y), lambda v, z: z == (v[0] ^ v[1])),
        "fork": relation(r, (r, r), lambda v, z: z == (v[0] & v[1])),
        "red": relation(r, (r,), lambda v, z: v[0] == 1 or z == 0),
        "blue": relation(r, (r,), lambda v, z: v[0] == 1 or z == 1),
        "erase": relation(r, (), lambda v, z: True),
    }
    beta = dict(alpha, red=alpha["blue"])
    for ass in (alpha, beta):
        for name, g in gs.items():
            g.validate_image(ass[name])
    lx, lr, ly = Leaf(x), Leaf(r), Leaf(y)
    base = Node(gs["root"], (lx, Node(gs["tail"], (Node(gs["fork"], (lr, lr)), ly))))
    red, blue, erase = [corolla(gs[name]) for name in ("red", "blue", "erase")]
    nested = graft(base, (lx, red, blue, ly))
    swapped = graft(base, (lx, blue, red, ly))
    erased = graft(base, (lx, erase, blue, ly))
    erased_both = graft(base, (lx, erase, erase, ly))
    assert base.profile.components == (x, r, r, y)
    assert nested.profile == swapped.profile == base.profile
    assert nested != swapped
    assert erased.profile.components == (x, r, y)
    assert erased_both.profile.components == (x, y)

    samples = {"red_corolla": red, "blue_corolla": blue, "nullary_corolla": erase,
               "mixed_four_leaf_base": base, "independent_red_blue": nested,
               "swapped_blue_red": swapped, "erase_first_repeated": erased,
               "erase_both_repeated": erased_both, "identity_r": lr}
    tables = {}
    comparison_count = 0
    identity_images = {name: corolla(g) for name, g in gs.items()}
    swap_image = dict(identity_images, red=blue)
    for name, t in samples.items():
        assert syntax_extend(t, identity_images) == t
        for ass_name, ass in (("alpha", alpha), ("beta", beta)):
            result = recursive_eval(t, ass)
            assert result == global_eval(t, ass)
            tables[f"{name}/{ass_name}"] = describe_relation(result)
            comparison_count += 1
        mapped = syntax_extend(t, swap_image)
        assert recursive_eval(mapped, alpha) == recursive_eval(t, beta)
    assert syntax_extend(red, swap_image) == blue and red != blue
    assert syntax_extend(nested, swap_image) != nested
    assert recursive_eval(red, alpha).outcomes((0,)) == [0]
    assert recursive_eval(red, beta).outcomes((0,)) == [1]
    assert recursive_eval(nested, alpha).outcomes((0, 0, 0, 0)) == [0]
    assert recursive_eval(nested, beta).outcomes((0, 0, 0, 0)) == [1]
    assert recursive_eval(nested, alpha).outcomes((0, 0, 1, 0)) == [0]
    assert recursive_eval(swapped, alpha).outcomes((0, 0, 1, 0)) == [0, 1]

    wrong_output = Component("b", "b", "r_parallel_whole")
    wrong_profile = relation(whole, (x, y), lambda v, z: True)
    rejections = [
        expect_rejection("parallel output component is not declared output",
            lambda: gs["red"].validate_image(identity(wrong_output))),
        expect_rejection("same endpoint but different full intermediate component",
            lambda: gs["root"].validate_image(wrong_profile)),
        expect_rejection("reversed root input order",
            lambda: Profile("a", "c", (tail, x))),
        expect_rejection("empty profile with nonloop output",
            lambda: Relation(x, Profile("a", "a", ()), 3)),
        expect_rejection("wrong output at repeated occurrence",
            lambda: compose(alpha["fork"], (identity(r), identity(x)))),
        expect_rejection("wrong primitive arity",
            lambda: gs["red"].validate_image(alpha["fork"])),
        expect_rejection("wrong syntax child order",
            lambda: Node(gs["root"], (Leaf(tail), Leaf(x)))),
    ]

    # Mutant 1: same-colored occurrences share ONE intermediate value. This is
    # not a second encoding of (1): it deliberately destroys occurrence linearity.
    fork = alpha["fork"]
    correct = compose(fork, (alpha["red"], alpha["blue"]))
    mutant_rows = []
    for xs in product(VALUES, repeat=2):
        outs = [z for z in VALUES if any(
            y0 == y1 and z in fork.outcomes((y0, y1))
            for y0 in alpha["red"].outcomes((xs[0],))
            for y1 in alpha["blue"].outcomes((xs[1],)))]
        mutant_rows.append((xs, outs))
    assert correct.outcomes((0, 0)) == [0]
    assert dict(mutant_rows)[(0, 0)] == []
    # Mutant 2: swap legal same-colored child positions. The full profile still
    # type-checks, but the result must not be silently identified.
    swapped_rel = compose(fork, (alpha["blue"], alpha["red"]))
    assert correct.outcomes((0, 1)) == [0]
    assert swapped_rel.outcomes((0, 1)) == [0, 1]
    # Mutant 3: use universal unary relation in place of equality identity.
    bad_unit = relation(r, (r,), lambda v, z: True)
    assert compose(alpha["red"], (bad_unit,)) != alpha["red"]

    return {
        "interfaces": ["a", "b", "c"], "carrier_each_component": [0, 1],
        "signature_matches": "audit/WorkstreamAReview.lean schema (read-only reference)",
        "signature": {name: {"output": g.output.name,
                             "profile": [c.name for c in g.profile.components]}
                      for name, g in gs.items()},
        "alpha_generator_relations": {k: describe_relation(v) for k, v in alpha.items()},
        "beta_change": "Only red is assigned alpha(blue); all other images unchanged.",
        "tables": tables,
        "independent_tree_oracle_comparisons": comparison_count,
        "syntax_identity_and_change_of_assignment_comparisons": len(samples),
        "distinguishing_witnesses": {
            "corolla": {"input": [0], "alpha_outputs": [0], "beta_outputs": [1]},
            "nested_four_leaves": {"input": [0, 0, 0, 0], "alpha_outputs": [0], "beta_outputs": [1]},
            "repeated_occurrence_swap": {"input": [0, 0, 1, 0],
                                         "red_blue_outputs": [0], "blue_red_outputs": [0, 1]}},
        "negative_typing_certificates": rejections,
        "mutation_controls": [
            {"mutation": "identify intermediate values at identical-color occurrences",
             "input": [0, 0], "correct_outputs": [0], "mutant_outputs": [], "detected": True},
            {"mutation": "swap legal same-colored replacements",
             "input": [0, 1], "correct_outputs": [0], "mutant_outputs": [0, 1], "detected": True},
            {"mutation": "replace equality identity by universal unary relation",
             "correct_mask": alpha["red"].mask,
             "mutant_mask": compose(alpha["red"], (bad_unit,)).mask, "detected": True}],
        "status": "PASS",
    }


def exhaustive_checks():
    """All Boolean relations in a precisely stated closed three-level domain.

    Outer arity n<=2; each middle arity m_i<=1; each bottom arity l_ij<=1.
    Every relation table at every vertex ranges over ALL possible subsets.
    Flattened arity stays <=2. Nullary choices are fully included at all levels.
    """
    start = time.monotonic()
    small = tuple((n, mask) for n in (0, 1) for mask in range(1 << (1 << (n + 1))))
    all_outer = tuple((n, mask) for n in (0, 1, 2)
                      for mask in range(1 << (1 << (n + 1))))
    unit_count = 0
    comparisons = 0
    for n, outer in all_outer:
        assert join_mask(n, outer, ((1, 9),) * n) == (n, outer)
        assert join_mask(1, 9, ((n, outer),)) == (n, outer)
        unit_count += 2
        for middle in product(small, repeat=n):
            got = join_mask(n, outer, middle)
            wanted = truth_mask(n, outer, middle)
            assert got == wanted, (n, outer, middle, got, wanted)
            comparisons += 1
    # Precompute the RHS composed-middle family for every possible bottom
    # family. Each equation is still tested for every independent outer table.
    shapes = {}
    for n in (0, 1, 2):
        records = []
        for middle in product(small, repeat=n):
            m = sum(a for a, _ in middle)
            for bottom in product(small, repeat=m):
                pos = 0
                replacement = []
                for arity, mask in middle:
                    replacement.append(join_mask(arity, mask, bottom[pos:pos+arity]))
                    pos += arity
                records.append((middle, bottom, tuple(replacement)))
        shapes[n] = records
    assoc_count = 0
    assoc_by_outer = {}
    for n in (0, 1, 2):
        count = 0
        for outer in range(1 << (1 << (n + 1))):
            for middle, bottom, replacement in shapes[n]:
                mid_arity, mid_mask = join_mask(n, outer, middle)
                lhs = join_mask(mid_arity, mid_mask, bottom)
                rhs = join_mask(n, outer, replacement)
                assert lhs == rhs, (n, outer, middle, bottom, lhs, rhs)
                count += 1
        assoc_by_outer[str(n)] = count
        assoc_count += count
    assert comparisons == 102724
    assert unit_count == 552
    assert assoc_count == 26879044
    return {"domain": {
                "carrier": [0, 1],
                "outer_arity": [0, 1, 2],
                "middle_arity_each_slot": [0, 1],
                "bottom_arity_each_middle_slot": [0, 1],
                "relation_choices": "Every subset of Bool^arity × Bool at every vertex; independent per occurrence.",
                "typing": "Masks are transportable to any legal endpoint-typed tree shape in this arity domain; typed mixed witnesses are separately checked."},
            "exhaustive_join_vs_truth_comparisons": comparisons,
            "exhaustive_unit_equalities": unit_count,
            "exhaustive_associativity_equalities": assoc_count,
            "associativity_count_by_outer_arity": assoc_by_outer,
            "cached_join_table_size": join_mask.cache_info().currsize,
            "runtime_seconds": round(time.monotonic() - start, 3),
            "status": "PASS"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=FilePath)
    parser.add_argument("--skip-exhaustive", action="store_true",
                        help="Smoke only; never label its output exhaustive evidence.")
    args = parser.parse_args()
    report = {"schema": "workstream-A-relational-evidence-v1", "evidence_class": "C",
              "status": "AUTHOR TESTED; NOT INDEPENDENTLY ACCEPTED",
              "python": platform.python_version(),
              "oracle_source_sha256": hashlib.sha256(FilePath(__file__).read_bytes()).hexdigest(),
              "finite_model": finite_model()}
    if args.skip_exhaustive:
        report["exhaustive"] = {"status": "NOT RUN"}
    else:
        report["exhaustive"] = exhaustive_checks()
    out = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(out)
    print(json.dumps({"finite_model": report["finite_model"]["status"],
                      "exhaustive": report["exhaustive"],
                      "output": str(args.output) if args.output else None}, indent=2))

if __name__ == "__main__":
    main()
