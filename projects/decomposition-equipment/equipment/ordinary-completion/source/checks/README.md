# E4 bounded ordinary-completion checks

These are finite **C** certificates for the unmarked C5 free virtual-to-ordinary
envelope family. They are not an implementation or decision procedure for the
entire free term quotient, a proof of its universal property, or a new full Lean
mechanization. The uniform completion and preservation arguments belong to P.

## Replay

Python 3 standard library only. From any extracted package root, run:

```
python -B checks/run_e4_checks.py --output /tmp/e4-finite-receipt.json
python -B checks/test_e4_guards.py --output /tmp/e4-guard-receipt.json
```

Use an output outside this package and all protected original source trees. Source,
manifest, directory, symlink and hard-link aliases are rejected. The original
source-tree path guards are lexical even if those directories do not exist, so
standalone receipt bytes do not depend on their presence. Both receipts bind
the exact atomic `source_scope_manifest.json` and every declared finite source.
The runner unsets inherited `PYTHONOPTIMIZE`, checks actual interpreter flags, and
requires byte-identical normal, `-O`, and `-OO` results. All checks use explicit
exceptions, never Python `assert`.

`dependencies/e3_model_cells.py` is an exact 32,540-byte frozen copy of the original
E3 checked source, SHA-256
`5941532e760980f0324a958d094e06396010c4d88db7883caa0008ed3edcbfcb`.
Only its graph, finite groupoid, finite function/span and original C5-cell primitives
are reused. Its expensive aggregate suite is not rerun or counted as new E4 evidence.
No external runtime files, packages, web services, or mutable path overrides are used.

## Actual semantic scope

- Unnormalized planar graph-word forests retain every root allocation, empty graph
  occurrence, ordered block, retained whole and local refinement slot.
- Actual horizontals pair graph words with finite spans. Actual cells consist of a
  graph forest, a typed endpoint-compatible function on the full tuple pullback,
  and one **global** scalar in C2 with an absorbing zero.
- Composites concatenate words and use tuple-span apexes; alternative choices use
  reordered/tagged apexes and invertible scalar weights. Every enumerated complete
  contextual cell fibre is bijective under precomposition, including empty paths,
  singleton paths, two-sided surrounding contexts and noninjective outer boundary
  maps. This checks real factor maps, not mere formal composite names.
- Associators and unitors are actual unary cells between differently nested tuple
  spans. Pentagon includes tensor-whiskered associators; triangle includes actual
  unitors. Three-choice cocycles retain both coefficient and scalar corrections.
- Old full profiles are enumerated for graphs of sizes 0–3 and arities 1–3. The
  principal N=6 example has three interfaces, nontrivial grades, repeated equal
  nonempty middle edge components, opposite occurrence-indexed refinements, and
  two cross-edge wholes. Actual proper-interval scalar factor pairs are preserved.
  The absorbing scalar also exhibits the forbidden cancellation if arbitrarily
  marked old witnesses are forced to become universal.
- The genuine unchanged old path of two singleton components reaches both a two-
  vertex edgeless whole and its edge-added whole. No single graph grade can receive
  that path and factor both targets through unary cells. The uniform exclusion of
  **every V horizontal term**, not only enumerated grades, is the separate P graph-
  grading invariant; this script does not infer nonrepresentability by transporting
  it backwards along a non-conservative functor.
- The completed graph-word horizontal has two occurrences and factors both wholes.
  It is not isomorphic to a one-occurrence old whole. The new empty-word unit is
  not silently identified with the old one-entry empty graph.
- Bad proposed whole-, cut-witness-, and scalar-forgetting quotients explicitly
  collide distinct original data. Rel and graph-free Span are regression only.

The graph-word equipment is a separating ordinary semantic model, **not** asserted
to equal the free completion. In particular the single-graph GraphSpan model does
not embed in it by a unit-preserving virtual-equipment map: its old empty graph
unit would map to a nonunit one-entry word. No such comparison is used here.

## Semantic mutations and guards

Ten mutations alter actual composite occurrence retention, tuple coefficient
factorization, scalar factors, choice comparison scalars, whole graphs, ordered
partitions, old scalars, refinement occurrence tuples, nullary scalar substitution,
and forest root allocations. Every mutation must be rejected in all three modes
with deterministic JSON and no uncaught exception/traceback.

Guard tests use disposable copies only. In all three modes they reject protected
output destinations, source/dependency drift, missing/extra manifest paths, wrong
schema and source symlinks. Direct subprocesses reject falsely claimed optimization
levels. A complete replay with inherited `PYTHONOPTIMIZE=2` proves the runner resets
its child modes. Final source bytes are checked again after every complete replay.

The atomic manifest freezes only this finite-source scope. The encompassing
mathematical report/archive may bind additional proof and audit files separately.
