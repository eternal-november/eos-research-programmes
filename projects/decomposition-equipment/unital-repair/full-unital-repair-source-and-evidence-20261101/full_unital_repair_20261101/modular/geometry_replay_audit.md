# Independent finite geometry replay audit

Reviewer: `modular_geometry_proof_check`, 2026-11-01 UTC.

Final independently replayed checker SHA-256:
`5b20275bb010cc3a996959f128246a53b5f4951076b731f33f983245258f4201`.

## Result

**PASS within the stated finite scope.** The original checker was inspected and
executed without source edits:

```sh
python ./full_unital_repair_20261101/modular/verify_modular_full_unital.py
```

Both the original and the corrected checker returned `PASS` and
**851,012 whole-factor records**, writing only its own
`modular_full_unital_results.json`. For each cyclic group C2–C5, ranks 1–4
cover 15 ordered positive compositions. The independent record-count formula is

`sum(n**(r+1) * (n+1)**(r-1) for r in range(1, 5))`.

This counts complete outer tuples and complete inner tuples over every ordered
positive grouping; the implementation uses the same parent `a[i]` for every
child in its block. Its signatures retain the entire outer operation class and
the ordered tuple of whole child-operation classes, not marginal leaf cuts.

## Independent checks and in-memory mutations

The following command was executed after the replay; it imports without running
`main` and does not write any file:

```sh
python - <<'PY'
import importlib.util, json
from pathlib import Path
p = Path('./full_unital_repair_20261101/modular/verify_modular_full_unital.py')
spec = importlib.util.spec_from_file_location('modular_review', p)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
report = json.loads(p.with_name('modular_full_unital_results.json').read_text())
for row in report['group_branching']:
    n = int(row['group'][1:]); R = row['rank_bound']
    expected = sum(n**(r+1) * (n+1)**(r-1) for r in range(1, R+1))
    assert row['whole_factor_records'] == expected
    assert row['groupings_checked'] == 2**R - 1
    assert row['actual_unary_identity_cut_checked'] is True
print('Independent enumeration-count formulas and U-report flags: PASS')

def unit_reflecting(classifier, n):
    by_class = {}
    for x in range(n):
        by_class.setdefault(classifier((x,)), set()).add(x == 0)
    return all(len(predicates) == 1 for predicates in by_class.values())

original = m.tuple_class
for n in (2, 3, 4, 5):
    assert unit_reflecting(original, n)
assert original(()) == ()
print('Explicit unary old-identity U predicates, C2-C5: PASS; empty identity unique')

m.tuple_class = lambda values: values
try:
    m.group_geometry(2, 2)
except AssertionError as e:
    print('Mutation exact factor classes / fixed indiscrete rank>=2 source: REJECTED:', e)
else:
    raise AssertionError('Invalid source/output-class prescription escaped')

unit_blind = lambda values: values if len(values) <= 0 else ('ignored',)
m.tuple_class = unit_blind
assert not unit_reflecting(unit_blind, 2)
try:
    m.group_geometry(2, 2)
except AssertionError as e:
    print('Mutation rank<=0 exact: REJECTED BY MAIN CHECKER:', e)
else:
    raise AssertionError('Non-unit-reflecting partition escaped')
m.tuple_class = original
print('Independent focused audit: PASS')
PY
```

Observed output:

```text
Independent enumeration-count formulas and U-report flags: PASS
Explicit unary old-identity U predicates, C2-C5: PASS; empty identity unique
Mutation exact factor classes / fixed indiscrete rank>=2 source: REJECTED: branch lift failed in C2, shape (1, 1)
Mutation rank<=0 exact: REJECTED BY MAIN CHECKER: full-unital identity cut failed in C2
Independent focused audit: PASS
```

The first mutation deliberately makes the *output factor classes* exact while
the checker retains its fixed indiscrete high-rank *source* requirement. It is
an invalid source/output-class prescription, not a counterexample to stability
of the fully discrete partition and not a mutation of the group law.

## Found-and-fixed coverage gap

The initially inspected checker (SHA-256
`4bfc789abffabda135e407e5b7cdeef2c5f262dc3371927d3e8c9d45630e7b7e`)
did not explicitly test U in `group_geometry`. Its original rank-one exactness
made U reflection immediate mathematically, but the rank-zero-exact mutation
passed the positive-cut checker and failed the independent U predicate check.
The author added the actual unary identity predicate to `group_geometry`.
The final independent replay and mutation above verify that the main checker
now rejects this mutation directly. No original checker source was changed by
this reviewer.

## Additional noncommutative finite support

Independently enumerated S3 under permutation composition `a[b[k]]`, with exact
rank-one classes and ignored higher-rank classes, over ranks 1–3. All seven
positive shapes passed; the 65,052 whole-factor records independently match
`sum(6**(r+1) * 7**(r-1) for r in range(1, 4))`. Noncommutativity of the table
was asserted before enumeration. This additional test did not edit or extend
the main checker or its report.

Exact standalone command executed:

```sh
python - <<'PY'
from itertools import permutations, product
from importlib.util import spec_from_file_location, module_from_spec
p = './full_unital_repair_20261101/modular/verify_modular_full_unital.py'
s = spec_from_file_location('review', p); m = module_from_spec(s); s.loader.exec_module(m)
G = tuple(permutations(range(3))); ix = {g:i for i,g in enumerate(G)}
table = tuple(tuple(ix[tuple(a[b[k]] for k in range(3))] for b in G) for a in G)
assert any(table[a][b] != table[b][a] for a,b in product(range(6), repeat=2))
count = 0; shapes = 0
for r in range(1,4):
    xs = tuple(product(range(6), repeat=r))
    for shape in m.compositions(r):
        signatures = {x:set() for x in xs}
        for a in product(range(6), repeat=len(shape)):
            for b in xs:
                out = []; children = []; offset = 0
                for i,size in enumerate(shape):
                    chunk = b[offset:offset+size]
                    out.extend(table[a[i]][v] for v in chunk)
                    children.append(m.tuple_class(chunk)); offset += size
                signatures[tuple(out)].add((m.tuple_class(a), tuple(children)))
                count += 1
        if r >= 2:
            assert len({frozenset(v) for v in signatures.values()}) == 1
        shapes += 1
assert count == sum(6**(r+1)*7**(r-1) for r in range(1,4)) == 65052
assert shapes == 7
print(f'Independent noncommutative S3 positive-cut audit: PASS, {shapes} shapes, {count} whole-factor records')
PY
```

Observed output:

```text
Independent noncommutative S3 positive-cut audit: PASS, 7 shapes, 65052 whole-factor records
```

## Coverage limits

- The arithmetic rank assertion checks compressed positive shapes, not actual
  typed graph substitution or empty-position records. Preservation of those
  records and nonerasing rank monotonicity remain mathematical proof obligations.
- The main checker enumerates cyclic groups C2–C5 and ranks at most four;
  the independent extra check enumerates S3 through rank three. General groups,
  arbitrary old profiles, empty-slot placement, and unbounded finite depth
  remain covered by the companion proof, not these finite enumerations.
- The imported external-unitization base is consumed by the original checker;
  this audit does not independently reconstruct that base.
