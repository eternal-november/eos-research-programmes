"""Author regression of selected path lifting, separate from independent checks."""
from itertools import product
import json, hashlib
from pathlib import Path


def require(test, message):
    if not test:
        raise RuntimeError(message)

n, m = 4, 2
u, v = n, m

def hd(x):
    return v if x == u else x % m

def sec(y):
    return u if y == v else y

def mul(xs, unit):
    return next((x for x in xs if x != unit), unit)

def lift(xs, source):
    require(hd(source) == mul(xs, v), 'ineligible source')
    first = next((i for i, x in enumerate(xs) if x != v), None)
    return tuple(source if i == first else sec(x) for i, x in enumerate(xs))

records = contractions = insertions = 0
for length in range(7):
    for path in product(range(m + 1), repeat=length):
        for source in range(n + 1):
            if hd(source) != mul(path, v):
                continue
            full = lift(path, source)
            require(mul(full, u) == source, 'wrong composite')
            require(tuple(map(hd, full)) == path, 'wrong target factors')
            records += 1
            for a in range(length):
                for b in range(a + 1, length + 1):
                    contracted = path[:a] + (mul(path[a:b], v),) + path[b:]
                    concrete = full[:a] + (mul(full[a:b], u),) + full[b:]
                    require(lift(contracted, source) == concrete, 'contraction naturality')
                    contractions += 1
            for i in range(length + 1):
                expanded = path[:i] + (v,) + path[i:]
                concrete = full[:i] + (u,) + full[i:]
                require(lift(expanded, source) == concrete, 'unit insertion naturality')
                insertions += 1

# A genuinely non-surjective full-unital interface C3 -> C3 x {1,0}.
# 1 is the boolean identity, 0 is absorbing.
E = tuple(product(range(3), range(2)))
def ep(xs):
    a, b = 0, 1
    for c, d in xs:
        a, b = (a + c) % 3, b * d
    return a, b
allowed = 0
for length in range(5):
    for path in product(E, repeat=length):
        if ep(path)[1] != 1:
            continue
        require(all(x[1] == 1 for x in path), 'factor closure')
        require(sum(x[0] for x in path) % 3 == ep(path)[0], 'unique lift product')
        allowed += 1

report = {
    'status': 'Author coherence regressions passed',
    'left_zero_source_nonunits': n,
    'left_zero_target_nonunits': m,
    'max_path_vertices': 6,
    'source_fixed_records': records,
    'all_interval_contractions': contractions,
    'unit_insertions': insertions,
    'factor_closed_C3_into_C3_times_boolean_chains_vertices_0_to_4': allowed,
    'scope': 'Finite regression only; no all-tree conclusion inferred from enumeration',
    'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
Path(__file__).with_name('selected_lifting_coherence_results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
