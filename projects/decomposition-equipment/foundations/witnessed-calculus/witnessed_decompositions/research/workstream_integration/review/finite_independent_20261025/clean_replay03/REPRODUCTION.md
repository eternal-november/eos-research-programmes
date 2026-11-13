# Finite integration reproduction

This directory supports the separately proved A4/C5/B3 integration. Read the
hash-frozen `DOMAIN.md` and `ExecutionRelease.json` first. The target domain is
not selected after observing outcomes. The parent released C execution at
2026-10-25T01:01:45Z for DOMAIN SHA256
`d01495686d5f3f01cc635061d7789f64ab0cf5a370571d144971cb819dba52fa`.

Only Python's standard library is required. From a fresh copied directory:

    python -u check_integration.py > AuthorRun.log 2>&1
    python -u run_mutations.py > MutationRun.log 2>&1

Run mutation replay only after the unmutated checker passes. Both scripts
produce JSON certificates next to themselves; the second script makes actual
source copies/edits under `mutations/` and retains the traceback of every
expected failed run. `model.py` and `check_integration.py` must come from the
same frozen source snapshot. Running an old bytecode cache instead of the
sources is not a new reproduction; use a fresh directory without __pycache__.

The main checker executes named adversarial controls, all 112,785 critical-
shape instances prescribed by T, the finite contextual/mixed path suite X,
the exhaustive hom/catalog domain H and composition subdomain, and the
independent factorization-candidate comparison F. That T count is an a priori
formula expectation, not a report that a pending run passed. The certificate
reports the actual count for every row and asserts agreement with the formula.
No term depth/arity bound is imposed on the mathematical theorem by these
finite tests.

Three distinct implementations compare tree/flat meanings: recursive local
substitution evaluation, a root-address leaf traversal, and operation-only flat
substitution. The hom checker compares a target-run decoder against independent
local-operation catalog tuples, not against itself. Factorization compares an
explicit forced-union decoder with brute enumeration of candidate intermediate
graphs and partitions. These are author-owned redundant checks. Independent
authorship and clean replay are separate acceptance evidence.

Path normal forms retain the raw forest at the ORIGINAL source occurrences
and use syntactic term normalization at its entries. Tests compare explicit
instances of the independently declared local relations, including the chosen
18 joining rule words. They do not define the category's arrow equality as
semantic equality and do not prove its unrestricted coherence. Missing-MIn
validator rejection is a syntactic coverage control; the mathematical necessity
of mixed relations is the separate P raw-added-vertex argument.

Whole graphs/grades, per-entry profiles, partitions, arrows and monoid values
are all retained in arrow keys. The family of monoid labels is a standard
scalar enrichment; none of these finite computations gives it independent
scientific significance, or activates later F/B4/D/E/G/I obligations.
