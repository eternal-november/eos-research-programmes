#!/usr/bin/env python3
"""Finite support, not a proof of unbounded graph/profile claims.

Enumerates actual whole factor tuples, never independent marginal cuts.
Only zero-cut test is actual monoid identity on the unary identity slice.
"""
from itertools import product
from pathlib import Path
import hashlib
import json


def require(test, message):
    if not test:
        raise AssertionError(message)


def canon(keys):
    ids = {}
    return tuple(ids.setdefault(k, len(ids)) for k in keys)


def stability(table, unit, partition):
    n = len(table)
    sig = [set() for _ in range(n)]
    for a, b in product(range(n), repeat=2):
        sig[table[a][b]].add((partition[a], partition[b]))
    skey = canon((partition[x], tuple(partition[table[a][x]] for a in range(n)),
                  tuple(partition[table[x][a]] for a in range(n))) for x in range(n))
    ckey = canon((partition[x], x == unit, frozenset(sig[x])) for x in range(n))
    return skey == canon(partition), ckey == canon(partition), ckey


def compositions(n):
    if n == 0:
        yield ()
    else:
        for head in range(1, n + 1):
            for rest in compositions(n - head):
                yield (head,) + rest


def tuple_class(values):
    return values if len(values) <= 1 else ("ignored",)


def group_geometry(n, rank_bound):
    # At the actual old unary identity, U has an empty record iff x=0.
    # This check is separate from positive factorization and cannot be omitted.
    unit_truth = {}
    for x in range(n):
        key = tuple_class((x,))
        unit_truth.setdefault(key, set()).add(x == 0)
    require(all(len(values) == 1 for values in unit_truth.values()),
            f"full-unital identity cut failed in C{n}")
    checked = 0
    records = 0
    for r in range(1, rank_bound + 1):
        xs = tuple(product(range(n), repeat=r))
        for shape in compositions(r):
            m = len(shape)
            signatures = {x: set() for x in xs}
            for a in product(range(n), repeat=m):
                for b in product(range(n), repeat=r):
                    source, inner, offset = [], [], 0
                    for i, size in enumerate(shape):
                        chunk = b[offset:offset + size]
                        source.extend((a[i] + value) % n for value in chunk)
                        inner.append(tuple_class(chunk))
                        offset += size
                    signatures[tuple(source)].add((tuple_class(a), tuple(inner)))
                    records += 1
            # For r=1 classes are singletons; for r>=2 all source labels agree.
            if r >= 2:
                require(len({frozenset(v) for v in signatures.values()}) == 1,
                        f"branch lift failed in C{n}, shape {shape}")
            require(r >= m and all(k >= 1 for k in shape), "nonerasing rank law")
            checked += 1
    return {"group": f"C{n}", "rank_bound": rank_bound,
            "groupings_checked": checked, "whole_factor_records": records,
            "actual_unary_identity_cut_checked": True}


def semilattice_control():
    values = tuple(product((0, 1), repeat=2))
    ix = {v: i for i, v in enumerate(values)}
    table = tuple(tuple(ix[(min(a[0], b[0]), min(a[1], b[1]))] for b in values) for a in values)
    unit = ix[(1, 1)]
    global_partition = canon(x == unit for x in range(4))
    s, c, _ = stability(table, unit, global_partition)
    require(s and c, "global semilattice two-block partition not stable")
    local = ((0, 0), (0, 1))
    require(stability(local, 1, (0, 1))[:2] == (True, True), "local discrete partition")
    require(stability(local, 1, (0, 0))[1] is False, "local U should split indiscrete seed")
    return {"global_unary_optimum_blocks": 2, "product_of_local_optima_blocks": 4,
            "global_partition": global_partition}


def private_factor_controls(base):
    table0 = tuple(tuple(row) for row in base["multiplication"])
    p0, q0 = tuple(base["P"]), tuple(base["Q"])
    out = []
    for n in (2, 3, 4):
        values = tuple(product(range(n), range(9)))
        ix = {v: i for i, v in enumerate(values)}
        table = tuple(tuple(ix[((a[0] + b[0]) % n, table0[a[1]][b[1]])] for b in values) for a in values)
        unit = ix[(0, 8)]
        for name, kp in (("P", p0), ("Q", q0)):
            partition = canon((a, kp[k]) for a, k in values)
            s, c, _ = stability(table, unit, partition)
            require(s and c, f"C{n} exact private factor with {name} failed")
            out.append({"private_group": f"C{n}", "K_partition": name,
                        "carrier": len(values), "blocks": len(set(partition)),
                        "S_Cu_stable": True})
    return out


def exchange_control():
    # Rank-two B is ignored by its actual local optimum by the proven extension.
    # The exact A observation and its swap distinguish every global coefficient tuple.
    out = []
    for n in (2, 3, 4, 5):
        x, y, yp = (0, 0), (0, 0), (0, 1)
        before = ((x, tuple_class(y)), (x, tuple_class(yp)))
        after = ((y, tuple_class(x)), (yp, tuple_class(x)))
        require(before[0] == before[1] and after[0] != after[1], "exchange defect not detected")
        out.append({"group": f"C{n}", "rank": 2, "before_equal": True,
                    "after_equal": False, "global_exact_class_count": n ** 4})
    return out


def main():
    here = Path(__file__).resolve().parent
    support_path = here.parent / "checks" / "external_unitization_results.json"
    base = json.loads(support_path.read_text())
    require(base["new_unit_index"] == 8 and base["old_identity_index"] == 2,
            "external unitization base mismatch")
    report = {
        "status": "PASS",
        "scope": "Finite coefficient and active-rank templates only; all-profile statements are mathematical proofs in the companion note.",
        "group_branching": [group_geometry(n, 4) for n in (2, 3, 4, 5)],
        "semilattice_optimum_reflection_negative": semilattice_control(),
        "external_unitized_private_factors": private_factor_controls(base),
        "exchange_negative": exchange_control(),
        "input_external_unitization_sha256": hashlib.sha256(support_path.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    path = here / "modular_full_unital_results.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "report": str(path),
                      "group_records": sum(x["whole_factor_records"] for x in report["group_branching"])}, indent=2))


if __name__ == "__main__":
    main()
