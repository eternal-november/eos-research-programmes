#!/usr/bin/env python3
"""Independent exhaustive checks and native path extraction for the trace note.

No external dependencies. Run with Python 3. Outputs a JSON report and selected
native edge histories. This supplements, rather than replaces, the proofs.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import inf
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

@dataclass(frozen=True)
class Edge:
    name: str
    src: str
    label: str
    dst: str
    cost: int

@dataclass(frozen=True)
class Machine:
    initial: str
    finals: frozenset[str]
    edges: tuple[Edge, ...]


def dp(machines: tuple[Machine, ...], visible: str,
       alpha: dict[str, str], synchronize: bool) -> dict:
    """Layered shortest path, retaining native edge IDs and actual endpoints.

    For synchronize=False, a product step may have independent concrete labels
    with the same visible label. This computes the local-first comparison, not
    a licensed execution of the original synchronous wiring.
    """
    start = tuple(m.initial for m in machines)
    current = {start: (0, ())}
    for a in visible:
        nxt = {}
        for states, (cost, history) in current.items():
            choices = [tuple(e for e in m.edges
                             if e.src == s and alpha[e.label] == a)
                       for m, s in zip(machines, states)]
            for edges in product(*choices):
                if synchronize and len({e.label for e in edges}) != 1:
                    continue
                ends = tuple(e.dst for e in edges)
                value = cost + sum(e.cost for e in edges)
                if value < nxt.get(ends, (inf, ()))[0]:
                    nxt[ends] = (value, history + (edges,))
        current = nxt
    finals = [(value, states) for states, value in current.items()
              if all(s in m.finals for s, m in zip(states, machines))]
    if not finals:
        return {"cost": None, "witness": None}
    (cost, history), ends = min(finals, key=lambda pair: pair[0][0])
    component_paths = [[step[i].name for step in history]
                       for i in range(len(machines))]
    words = ["".join(step[i].label for step in history)
             for i in range(len(machines))]
    # Verify actual path composability and cost, independently of the DP.
    for i, machine in enumerate(machines):
        state = machine.initial
        for step in history:
            e = step[i]
            assert e.src == state
            state = e.dst
        assert state in machine.finals
    assert sum(e.cost for step in history for e in step) == cost
    if synchronize:
        assert len(set(words)) <= 1
    assert all("".join(alpha[b] for b in word) == visible for word in words)
    return {"cost": cost, "native_edge_paths": component_paths,
            "concrete_words": words, "actual_endpoints": list(ends),
            "is_original_native_synchronous_run": synchronize}


def exhaustive_scalar_obstruction():
    """Two-component four-point and three-component three-point fibers."""
    vals = (0, 1, 2, inf)
    profiles = tuple(product(vals, repeat=4))
    count = 0
    # Three profiles gives 16,777,216 triples; two suffice exhaustively, plus
    # exhaustive three profiles over a smaller three-point fiber below.
    for fs in product(profiles, repeat=2):
        minima = tuple(min(f) for f in fs)
        local = sum(minima)
        joint = min(sum(f[j] for f in fs) for j in range(4))
        assert local <= joint
        if all(m < inf for m in minima):
            common = any(all(f[j] == m for f, m in zip(fs, minima))
                         for j in range(4))
            assert (local == joint) == common
        else:
            assert local == joint == inf
        count += 1
    small = tuple(product((0, 1, inf), repeat=3))
    for fs in product(small, repeat=3):
        minima = tuple(min(f) for f in fs)
        local = sum(minima)
        joint = min(sum(f[j] for f in fs) for j in range(3))
        assert local <= joint
        if local < inf:
            common = any(all(f[j] == m for f, m in zip(fs, minima))
                         for j in range(3))
            assert (local == joint) == common
        else:
            assert joint == inf
        count += 1
    return count


def exhaustive_universal():
    profiles = tuple(product((0, 1, 2, inf), repeat=3))
    count = 0
    for f in profiles:
        const = len(set(f)) == 1
        exact_word_tests = all(f[j] == min(f) for j in range(3))
        all_partners = all(min(f[j]+g[j] for j in range(3)) == min(f)+min(g)
                           for g in profiles)
        assert const == exact_word_tests == all_partners
        count += len(profiles)
    return count


def words(alphabet: str, n: int):
    return ["".join(w) for k in range(n+1) for w in product(alphabet, repeat=k)]


def push(f, alpha):
    out = {}
    for w, val in f.items():
        v = "".join(alpha[b] for b in w)
        out[v] = min(out.get(v, inf), val)
    return out


def convolution(f, g, bound):
    out = {}
    for w, fw in f.items():
        for u, gu in g.items():
            if len(w+u) <= bound:
                out[w+u] = min(out.get(w+u, inf), fw+gu)
    return out


def check_convolution():
    alpha = {"0": "a", "1": "a", "2": "b"}
    concrete = words("012", 3)
    # Deterministic nonconstant profiles; include infeasibility independently.
    cases = 0
    for seed in range(32):
        f = {w: (inf if (sum(map(int,w))+len(w)+seed)%7 == 0
                 else (3*sum(map(int,w))+seed)%9) for w in concrete}
        g = {w: (inf if (2*sum(map(int,w))+seed)%5 == 0
                 else (len(w)+sum(map(int,w))+seed)%6) for w in concrete}
        lhs = push(convolution(f,g,3), alpha)
        rhs = convolution(push(f,alpha), push(g,alpha),3)
        assert lhs == rhs
        cases += len(lhs)
    return cases


def common_normalizers(machine, alpha, kappa):
    replacements = {}
    for e in machine.edges:
        candidates = [q for q in machine.edges if q.src == e.src and q.dst == e.dst
                      and q.label == kappa[alpha[e.label]] and q.cost <= e.cost]
        if not candidates:
            return None
        replacements[e.name] = min(candidates, key=lambda q:q.cost).name
    return replacements


def run_examples():
    alpha = {"0":"a", "1":"a"}
    K = 7
    first = Machine("s", frozenset({"s"}),
                    (Edge("left_0","s","0","s",1),
                     Edge("left_1","s","1","s",K+1)))
    second = Machine("t", frozenset({"t"}),
                     (Edge("right_0","t","0","t",K+1),
                      Edge("right_1","t","1","t",1)))
    rows=[]
    for n in range(21):
        local=dp((first,second),"a"*n,alpha,False)
        joint=dp((first,second),"a"*n,alpha,True)
        assert local["cost"] == 2*n
        assert joint["cost"] == (K+2)*n
        rows.append({"length":n,"local":local["cost"],"joint":joint["cost"],
                     "gap":joint["cost"]-local["cost"]})
    # An arbitrarily cyclic two-state machine: both colors toggle, while a
    # canonical 0-edge is cheaper and has the same actual endpoints.
    cyclic=Machine("q0",frozenset({"q0","q1"}),tuple(
        Edge(f"toggle_{s}_{b}",s,b,t,c)
        for s,t in (("q0","q1"),("q1","q0"))
        for b,c in (("0",2),("1",5))))
    assert common_normalizers(first,alpha,{"a":"0"}) is not None
    assert common_normalizers(second,alpha,{"a":"0"}) is None
    assert common_normalizers(second,alpha,{"a":"1"}) is not None
    assert common_normalizers(cyclic,alpha,{"a":"0"}) is not None
    positive=[]
    for n in range(21):
        local=dp((first,cyclic),"a"*n,alpha,False)
        joint=dp((first,cyclic),"a"*n,alpha,True)
        assert local["cost"] == joint["cost"] == 3*n
        assert joint["concrete_words"] == ["0"*n,"0"*n]
        positive.append(n)
    return {"K":K,"gap_family":rows,
            "gap_native_witness_length_4":dp((first,second),"aaaa",alpha,True),
            "incompatible_local_witnesses_length_4":dp((first,second),"aaaa",alpha,False),
            "positive_native_witness_length_5":dp((first,cyclic),"aaaaa",alpha,True),
            "positive_lengths_checked":positive,
            "canonical_replacement_table":common_normalizers(cyclic,alpha,{"a":"0"})}


def main():
    report={"scalar_profiles_checked":exhaustive_scalar_obstruction(),
            "universal_partner_checks":exhaustive_universal(),
            "sequential_convolution_values_checked":check_convolution(),
            "examples":run_examples(),"all_assertions_passed":True}
    path=HERE/"check_results.json"
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k != "examples"},indent=2))
    print(f"Full report and native witnesses: {path}")

if __name__=="__main__":
    main()
