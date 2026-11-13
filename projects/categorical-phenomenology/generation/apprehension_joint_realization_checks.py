"""Finite checks for joint realization of carrier-based apprehensions.

Each module is an apprehension P @ W with:
  content X       : assignments to that module's labelled ports;
  deriv W -> X    : restriction of a candidate whole assignment;
  occ P -> X      : the module's local port map.

A realization retains BOTH the whole assignment and the indexed local states.
The global verdict is computed by matching their exposed ports. No global
compatibility verdict is an input.

Run with Python 3.10+; no third-party dependencies are needed.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, permutations, product
from typing import Hashable, Iterable

Variables = tuple[str, ...]
Whole = tuple[int, ...]
Local = Hashable
Realization = tuple[Whole, tuple[Local, ...]]


@dataclass(frozen=True)
class Module:
    name: str
    ports: Variables
    # Rows are (local state, exposed port assignment).
    rows: tuple[tuple[Local, tuple[int, ...]], ...]

    def __post_init__(self) -> None:
        if len(set(self.ports)) != len(self.ports):
            raise ValueError("Ports must be distinct within a module.")
        if len({local for local, _ in self.rows}) != len(self.rows):
            raise ValueError("Each local state must have exactly one readout.")
        if any(len(values) != len(self.ports) for _, values in self.rows):
            raise ValueError("Readout arity does not match the module interface.")


def require(condition: bool, message: str) -> None:
    """Keep checks active even when Python is run with optimization."""
    if not condition:
        raise AssertionError(message)


def project(variables: Variables, whole: Whole, ports: Variables) -> tuple[int, ...]:
    index = {v: k for k, v in enumerate(variables)}
    return tuple(whole[index[v]] for v in ports)


def realize(
    variables: Variables, modules: tuple[Module, ...]
) -> set[Realization]:
    """Enumerate exact port-matching realizations over binary whole variables."""
    if len(set(variables)) != len(variables):
        raise ValueError("Whole-variable labels must be distinct.")
    if len({m.name for m in modules}) != len(modules):
        raise ValueError("Module identity must be retained, not silently duplicated.")
    if any(v not in variables for m in modules for v in m.ports):
        raise ValueError("A module port is missing from the whole interface.")
    answer: set[Realization] = set()
    for whole in product((0, 1), repeat=len(variables)):
        choices = [
            tuple(local for local, values in m.rows
                  if values == project(variables, whole, m.ports))
            for m in modules
        ]
        for locals_ in product(*choices):
            answer.add((whole, locals_))
    return answer


def glue_without_whole(
    variables: Variables, modules: tuple[Module, ...]
) -> set[Realization]:
    """Select local states, then identify shared ports: no whole state is guessed.

    Requires a covering family of interfaces. Under this condition each compatible
    family decodes to exactly one whole assignment.
    """
    if {v for m in modules for v in m.ports} != set(variables):
        raise ValueError("Interfaces must cover the whole variable set.")
    answer: set[Realization] = set()
    for chosen in product(*(m.rows for m in modules)):
        assigned: dict[str, int] = {}
        compatible = True
        for m, (_, values) in zip(modules, chosen):
            for v, value in zip(m.ports, values):
                if v in assigned and assigned[v] != value:
                    compatible = False
                    break
                assigned[v] = value
            if not compatible:
                break
        if compatible:
            whole = tuple(assigned[v] for v in variables)
            local_states = tuple(local for local, _ in chosen)
            answer.add((whole, local_states))
    return answer


def parity_module(name: str, ports: Variables, parity: int) -> Module:
    if len(ports) != 2 or parity not in (0, 1):
        raise ValueError("Parity modules need two ports and a bit.")
    return Module(name, ports, tuple((a, (a, a ^ parity)) for a in (0, 1)))


def all_subsets(n: int) -> Iterable[tuple[int, ...]]:
    for k in range(n + 1):
        yield from combinations(range(n), k)


def check_modular_gluing(variables: Variables, modules: tuple[Module, ...]) -> int:
    """Check R_(J union K) = R_J x_(R_(J intersect K)) R_K on witnesses.

    Comparison retains the whole state and all shared local states, not just
    their boundary observations.
    """
    subsets = tuple(all_subsets(len(modules)))
    by_subset = {
        indices: realize(variables, tuple(modules[i] for i in indices))
        for indices in subsets
    }
    checked = 0
    for js in subsets:
        for ks in subsets:
            union = tuple(sorted(set(js) | set(ks)))
            intersection = set(js) & set(ks)
            glued: set[Realization] = set()
            for wj, aj in by_subset[js]:
                left = dict(zip(js, aj))
                for wk, ak in by_subset[ks]:
                    right = dict(zip(ks, ak))
                    if wj != wk or any(left[i] != right[i] for i in intersection):
                        continue
                    combined = left | right
                    glued.add((wj, tuple(combined[i] for i in union)))
            require(glued == by_subset[union], f"Modular gluing failed: {js}, {ks}")
            checked += 1
    return checked


def main() -> None:
    variables = ("x", "y", "z")
    scopes = (("x", "y"), ("y", "z"), ("x", "z"))
    names = ("xy", "yz", "xz")
    triangle = tuple(parity_module(n, p, b)
                     for n, p, b in zip(names, scopes, (0, 0, 1)))
    require(len(realize(variables, ())) == 8, "Empty family must leave W unconstrained.")
    require(all(len(realize(variables, (m,))) == 4 for m in triangle), "Single count")
    require(all(len(realize(variables, pair)) == 2
                for pair in combinations(triangle, 2)), "Pair count")
    require(not realize(variables, triangle), "Odd-parity loop must be obstructed.")
    for m in triangle:
        for port in range(2):
            require({values[port] for _, values in m.rows} == {0, 1}, "Unary support")
    print("Odd triangle: 8 candidates; 4 states per one-module assembly; "
          "2 per two-module assembly; 0 for all three.")

    modular_cases = 0
    permutation_cases = 0
    for bits in product((0, 1), repeat=3):
        modules = tuple(parity_module(n, p, b) for n, p, b in zip(names, scopes, bits))
        actual = realize(variables, modules)
        expected_count = 2 if bits[0] ^ bits[1] ^ bits[2] == 0 else 0
        require(len(actual) == expected_count, f"Parity characterization failed: {bits}")
        require(actual == glue_without_whole(variables, modules), "Scaffold-free decoding")
        expected = {(w, tuple(zip(names, local))) for w, local in actual}
        for order in permutations(modules):
            got = set()
            for w, local in realize(variables, order):
                values = dict(zip((m.name for m in order), local))
                got.add((w, tuple((n, values[n]) for n in names)))
            require(got == expected, "Order independence failed.")
            permutation_cases += 1
        modular_cases += check_modular_gluing(variables, modules)
    print(f"All 8 parity regimes checked; {permutation_cases} module orders agree; "
          f"{modular_cases} overlapping-block gluing cases agree witness-for-witness.")

    # After joining the two copy modules, boundary x,z is diagonal. Retaining only
    # its separate unary projections fabricates the impossible continuation.
    first_two = realize(variables, triangle[:2])
    exact_boundary = {(w[0], w[2]) for w, _ in first_two}
    inverter = {values for _, values in triangle[2].rows}
    coarse_boundary = set(product({x for x, _ in exact_boundary},
                                 {z for _, z in exact_boundary}))
    require(exact_boundary == {(0, 0), (1, 1)}, "Exact boundary wrong")
    require(not exact_boundary & inverter, "Exact continuation should fail")
    require(coarse_boundary & inverter == {(0, 1), (1, 0)}, "Coarsening witness")
    print("Retention obstruction: replacing a joint boundary by unary possibilities "
          "creates two spurious boundary realizations.")

    # Multiplicity is semantic data, not an equality-proof artifact.
    copy = parity_module("copy", ("x", "z"), 0)
    tagged = Module("tagged", ("x", "z"),
                    tuple(((a, tag), (a, a)) for a, tag in product((0, 1), repeat=2)))
    base = realize(("x", "z"), (copy,))
    rich = realize(("x", "z"), (tagged,))
    require({w for w, _ in base} == {w for w, _ in rich}, "Visible sets differ")
    require(len(base) == 2 and len(rich) == 4, "Local multiplicity was lost")
    modular_cases_hidden = check_modular_gluing(("x", "z"), (tagged,))
    improper = {(w, a, b) for w, a in rich for v, b in rich if w == v}
    require(len(improper) == 8, "Expected two independent copies of hidden state")
    require(len(rich) == 4, "A shared module must retain one hidden witness")
    print("Hidden-state check: same 2 visible states, but 2 versus 4 realizations. "
          f"{modular_cases_hidden} shared-module gluing cases retain witness identity; "
          "matching only the visible whole would incorrectly yield 8.")
    print("All checks passed.")


if __name__ == "__main__":
    main()
