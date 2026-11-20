#!/usr/bin/env python3
"""Exact finite O7 marked-span certificate, given a legal raw-row relation."""
import argparse
import json
from collections import defaultdict, deque
from fractions import Fraction
from math import lcm


def rational(x):
    if type(x) not in (int, str):
        raise ValueError("use integers or strings for exact rationals")
    return Fraction(x)


def inputs(data):
    def rows(name):
        out = {}
        for r in data[name]:
            i = r["id"]
            if not isinstance(i, str) or i in out:
                raise ValueError("raw row IDs must be distinct strings per side")
            p, c = rational(r["mass"]), tuple(map(rational, r["cost"]))
            if p < 0 or any(x < 0 for x in c):
                raise ValueError("negative mass or cost")
            out[i] = p, c
        if sum(p for p, _ in out.values()) != 1:
            raise ValueError("each table must have total mass one")
        return out

    P, Q = rows("candidate"), rows("reference")
    if len({len(c) for _, c in list(P.values()) + list(Q.values())}) != 1:
        raise ValueError("all cost vectors must have the same dimension")
    R = set()
    for i, j in data["allowed"]:
        if i not in P or j not in Q:
            raise ValueError("relation uses unknown row ID")
        if any(a > b for a, b in zip(P[i][1], Q[j][1])):
            raise ValueError("declared legal pair increases candidate cost")
        R.add((i, j))
    return P, Q, R


def transportation(P, Q, R):
    D = lcm(*(p.denominator for p, _ in list(P.values()) + list(Q.values())))
    s, t = (0, ""), (3, "")
    res = defaultdict(dict)

    def edge(u, v, c):
        res[u][v], res[v][u] = c, 0

    for i, (p, _) in P.items():
        edge(s, (1, i), int(D * p))
    for i, j in sorted(R):
        edge((1, i), (2, j), D + 1)
    for j, (q, _) in Q.items():
        edge((2, j), t, int(D * q))

    val = 0
    while val < D:
        prev, queue = {s: None}, deque([s])
        while queue and t not in prev:
            u = queue.popleft()
            for v, c in res[u].items():
                if c > 0 and v not in prev:
                    prev[v] = u
                    queue.append(v)
        if t not in prev:
            A = sorted(i for k, i in prev if k == 1)
            B = sorted({j for i, j in R if i in A})
            a, b = sum((P[i][0] for i in A), Fraction()), sum((Q[j][0] for j in B), Fraction())
            assert a > b
            return None, {"candidate_subset": A, "neighbors": B,
                          "candidate_mass": str(a), "reference_mass": str(b)}
        path, v = [], t
        while v != s:
            u = prev[v]
            path.append((u, v))
            v = u
        inc = min(res[u][v] for u, v in path)
        for u, v in path:
            res[u][v] -= inc
            res[v][u] += inc
        val += inc
    return {(i, j): Fraction(res[(2, j)][(1, i)], D) for i, j in sorted(R)
            if res[(2, j)][(1, i)]}, None


def sparsify(flow):
    # Scan edges against a growing forest. The first redundant edge closes
    # an even cycle; eliminate it or another edge by an alternating move.
    while True:
        forest = defaultdict(list)
        for i, j in sorted(flow):
            x, y = (0, i), (1, j)
            prev, todo = {x: None}, [x]
            while todo and y not in prev:
                u = todo.pop()
                for v in forest[u]:
                    if v not in prev:
                        prev[v] = u
                        todo.append(v)
            if y not in prev:
                forest[x].append(y)
                forest[y].append(x)
                continue
            cycle, v = [(i, j)], y
            while v != x:
                u = prev[v]
                a, b = (u, v) if u[0] == 0 else (v, u)
                cycle.append((a[1], b[1]))
                v = u
            step = min(flow[e] for e in cycle[::2])
            for k, e in enumerate(cycle):
                flow[e] += step if k % 2 else -step
                if flow[e] == 0:
                    del flow[e]
            break
        else:
            return flow


def solve(data):
    P, Q, R = inputs(data)
    partners = {i: sorted(j for ii, j in R if ii == i) for i in P}
    missing = sorted(i for i in P if not partners[i])
    flow, cut = transportation(P, Q, R)
    if missing or cut is not None:
        return {"ok": False, "uncovered_candidate": missing, "deficient_cut": cut}
    sparsify(flow)
    witness = [(i, j, p) for (i, j), p in sorted(flow.items())]
    witness += [(i, partners[i][0], Fraction()) for i in sorted(P) if not P[i][0]]
    result = {"ok": True, "span": [{"candidate": i, "reference": j, "mass": str(p),
                                    "cost": list(map(str, Q[j][1]))}
                                   for i, j, p in witness]}
    if not verify(data, result):
        raise RuntimeError("internal certificate verification failed")
    return result


def verify(data, answer):
    P, Q, R = inputs(data)
    if not answer["ok"]:
        bad = answer["uncovered_candidate"]
        if len(set(bad)) != len(bad) or any(i not in P or any(a == i for a, _ in R) for i in bad):
            return False
        cut = answer["deficient_cut"]
        if cut is None:
            return bool(bad)
        A = set(cut["candidate_subset"])
        if not A <= P.keys() or len(A) != len(cut["candidate_subset"]):
            return False
        B = {j for i, j in R if i in A}
        a = sum(P[i][0] for i in A)
        b = sum(Q[j][0] for j in B)
        return (list(sorted(B)) == cut["neighbors"] and a > b and
                a == rational(cut["candidate_mass"]) and b == rational(cut["reference_mass"]))
    pm, qm = dict.fromkeys(P, Fraction()), dict.fromkeys(Q, Fraction())
    covered = set()
    for row in answer["span"]:
        i, j, w = row["candidate"], row["reference"], rational(row["mass"])
        if (i, j) not in R or w < 0 or tuple(map(rational, row["cost"])) != Q[j][1]:
            return False
        pm[i] += w
        qm[j] += w
        covered.add(i)
    return (covered == P.keys() and all(pm[i] == p for i, (p, _) in P.items())
            and all(qm[j] == p for j, (p, _) in Q.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="finite raw tables and allowed pair relation (JSON)")
    parser.add_argument("--verify", metavar="CERTIFICATE", help="verify an existing JSON certificate")
    args = parser.parse_args()
    try:
        with open(args.input, encoding="utf-8") as f:
            data = json.load(f)
        if args.verify:
            with open(args.verify, encoding="utf-8") as f:
                ok = verify(data, json.load(f))
            print(json.dumps({"valid": ok}))
            return 0 if ok else 1
        ans = solve(data)
        print(json.dumps(ans, indent=2))
        return 0 if ans["ok"] else 1
    except (ValueError, TypeError, KeyError, ZeroDivisionError) as exc:
        parser.exit(2, f"Invalid input or certificate: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
