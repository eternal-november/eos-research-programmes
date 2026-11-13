# Independent full unital finite verification

## Results and scope

All acceptance checks below passed in ordinary Python and under `python -O`; the paired result JSON files were byte-identical. The acceptance scripts use explicit exceptions rather than removable `assert` statements. They do not import any author implementation. Transformation monoids are built by actual composition; all cut signatures retain ordered whole factor tuples and their common concrete source.

These are finite checks, not proofs for all parameters, all old records, arbitrary generated depth, or unbounded empty insertion. Analytic claims must be supplied by the separate theorem authors. Original I1, I2 and I5 sources were read only. No file was uploaded.

**Unit-domain correction.** The first size-only diagnostic marked a zero-tree predicate on its `(1)` carrier but not its `(2)` carrier. That is not a valid interpretation of both carriers as terminal-grade whole-graph unary identities: a unary identity on a two-vertex graph also admits the zero tree. Its reported `[8,4,84]` result is retained only as a synthetic mask-sensitivity diagnostic, not evidence for the intended old-profile calculus. The acceptance test `verify_explicit_old_records.py` supersedes that interpretation. It derives unit capability from each complete old record and never from active size or active rank alone.

## Scalar transformation family

`verify_full_unital.py` independently generates `M_k=<a,b>` with identity, using actual transformations on `k` points, for every integer `4 <= k <= 128`. It verifies order `3k-2`, the literal identity, the submonoid/ideal observation `H={e,b,b^2}`, and the complete elementary-stage partitions.

The frozen elementary step retains the previous partition and adds both the joint binary factor-class signature and the literal zero-tree feasibility predicate in the **same** step. The starting partition is `P^(0)={H,M_k\H}`.

For all tested parameters, its stable partition has `2k` blocks: every `A_i` is a singleton; `{B_i,D_i}` is a block for `0 <= i <= k-3`; and `B_(k-2),B_(k-1)` are singletons. The complete stage shapes, not only their counts, match the proposed formulas. The verified counts are `2`, `4`, `min(2k-2,11)` at stages zero, one and two; from stage three onward they are `min(2k,2^(r+1)+6)`. The nontrivial-round count is `max(3,ceil(log2(k-3)))`.

The unit-aware closure of the top partition has the same endpoint. The original binary-only closure still has `k` blocks and is deliberately retained as a negative control for substituting the old answer. The initial partition is substitution-stable, while substitution closure after the new cut closure is discrete. The pair `b,b^2` agrees under the pure initial-context and pure unital-cut theories but is separated by right multiplication by `ab`, followed by the cut observation distinguishing the constants. The previously used pair `e,b` is not used as a mixed-only witness.

## Two channels at the actual unary identity

For every `4 <= k <= 12`, the checker enumerates actual ordered factor tuples in `M_k^2`. Its unit predicate is exactly `(e,e)`, not an independent predicate on each coordinate.

Starting from first-channel `H` membership, the stable unit-aware cut partition has `4k^2-2` blocks. It agrees with the tensor of the two scalar stable partitions except that all of `H^2\{(e,e)}` is one block. Thus the scalar tensor partition, which has `4k^2` blocks, is a checked negative control. In these tested identity-fibre cases, `C_u(TP)=T(C_u(P))=C_u(P)`. This is not asserted to prove global C/T commutation. Substitution after this cut closure is discrete.

## Literal old records and tagged empty positions

`verify_explicit_old_records.py` defines eight exact old records in a terminal-grade edgeless graph subdiagram:

- the empty nullary operation and the distinct empty identity;
- the whole-input unary identities on graphs `{0}`, `{1}` and `{0,1}`;
- the ordered two-branch partition `({0},{1})` of `{0,1}`;
- the genuine nonidentity partition `({0,1},empty)`;
- the genuine nonidentity partition `({0},empty,{1})`.

Vertices, ordered input subsets, edges, grade arrow and old scalar remain part of each record. Unit capability requires the actual one-input whole-graph identity with identity grade and unit old scalar. The two extra-empty-slot records therefore do not themselves admit a zero tree even though one has active rank one. Empty nullary and empty identity are not conflated. All seventeen induced graft/cut operations whose source and factors belong to this finite catalogue are tested.

For `M_4`, the whole-tuple C-only stage counts on the genuine two-branch record are `4 -> 16 -> 54 -> 70 -> 84`. Every actual nonempty unary identity reaches eight classes. The extra-empty rank-one record also reaches eight by its permitted cuts, without falsely declaring that record an identity. The combined S/C refinement reaches ten classes at every rank-one record and one hundred at every rank-two record. The M4 test evaluates 34,703 full records per pass.

The rank-sensitive `C4^2` quotient is checked against the same literal catalogue. It retains sixteen exact label states at rank one and sixteen quotient states over each 256-point rank-two fibre. Direct concrete-versus-quotient joint-cut decoder comparisons pass for 214,787 full records, as do composition descent and the literal unit decoder. The generated simultaneous S/C/T closure from first-channel parity is also computed independently: its eight-sort count vectors are `[1,1,2,2,2,4,2,4]`, then `[1,1,5,5,5,16,4,16]`, then `[1,1,16,16,16,16,16,16]`. The final complete partition equals the proposed rank-sensitive quotient, not merely its class counts.

Additional bounded empty-position checks in `verify_rank_sensitive_empties.py` cover twenty tagged size profiles with at most three positions and total active vertex size at most two: 232 operations and 10,243 full records. These are corroboration, not an empty-normalization theorem.

## Proper positive controls

`verify_rank_sensitive.py` checks the profile-dependent group quotient, with exact group labels at active rank one and coordinate quotient labels at larger rank. It enumerates 70,144 full records for `C4^2` through active size two and 7,408 for scalar `C4` through active size three. Its direct decoder check compares every concrete source fibre with the inverse fibre of the independently constructed quotient graft table. Whole-factor substitution, joint cuts, units and the declared channel swap pass. Branch reversal was also tested as a supplementary algebraic diagnostic, not as an additional declared transport obligation. The literal-old-record test above provides the stronger unit-domain acceptance check.

The uniform left-zero quotient family is a separate **unary-geometry** control, not a substitute for the branching quotient. The checker realizes `L_n^1` as `n` constant transformations plus the identity on `n+1` points. It verifies identity reflection and complete binary mapped fibres for all `1 <= m <= n <= 8` under the map `c_i -> c_(i mod m)`. For `L_4^1 -> L_2^1`, complete scalar chain records are compared for zero through six vertices, and squared-label chain records for zero through three vertices. The squared 25-state model has the expected nine-state simultaneous quotient.

The same uniform quotient fails branching: at concrete source `(c_0,c_2)`, the target record with common parent `d_0` and two identity children has marginal parent lifts `{c_0}` and `{c_2}`, but no common parent. This explicitly checks the distinction between joint and marginal lifting.

## Full unital modular negative control

`verify_external_unitization.py` repairs the original unary modular witness by adjoining a genuinely new identity to the original eight-element transformation monoid. It realizes the resulting nine-element monoid as actual transformations on nine points via the faithful left-regular action, with the extra point sent to the represented element. The old identity becomes a nonunit idempotent.

Each old local partition is extended by a singleton for the new literal identity. Both resulting three-block partitions are substitution-stable and full-unital-cut-stable. Their four-block intersection is substitution-stable, but one unital cut step refines it to six blocks. The checked witness is the pair of old source indices zero and one: `0*5=0`, while no element, including the new identity, satisfies `u*5=1`. This is a full-unital **unary** modular counterexample; no branching local-stability assertion is made.

## Mutation sensitive implementation rejection

The finite semantic counterexamples above are distinct from mutation detection. `verify_mutation_replay.py` copies the accepted explicit-old-record checker into temporary directories, verifies both unmodified controls against the accepted complete JSON, then changes exactly one code site per mutant. The accepted original is checked unchanged afterward. All four mutants are syntactically valid and are rejected by named mathematical checks in both normal and optimized Python:

- Removing the vertex-free U relation fails `generated closure differs from proposed quotient`.
- Using uniform group cosets at rank one fails `unit decoder not exact`.
- Excluding the size-two old unary identity fails `full old unit control`.
- Exchanging the empty identity and empty nullary classifications fails `nullary is not zero tree`.

The harness explicitly rejects missing-file, import, syntax and permission errors as invalid test outcomes. The receipt records the accepted checker/result hashes, each mutated code hash, both unmodified controls and all eight rejection traces. The harness itself was replayed under `-O` with byte-identical receipt output. Temporary mutated implementations are removed; none replaces an acceptance checker.

## Reproduction

Run from any directory:

```sh
python verify_full_unital.py --max-k 128 --product-max-k 12 --typed-max-k 8
python -O verify_full_unital.py --max-k 128 --product-max-k 12 --typed-max-k 8 --output full_unital_results_optimized.json
cmp full_unital_results.json full_unital_results_optimized.json
python verify_explicit_old_records.py
python verify_rank_sensitive.py
python verify_rank_sensitive_empties.py
python verify_external_unitization.py
python verify_mutation_replay.py
```

All paths above are relative to this `checks` directory. Ordinary-versus-optimized byte comparisons were also performed for each of the last four scripts. `python -m py_compile verify_*.py` checks syntax. Every result file records its checker SHA-256; the main result also pins the three original sources it inspected.

The old size-only diagnostic remains inside `full_unital_results.json` under `typed_active_size_templates` solely for reproducibility and must not be cited as a realized terminal-grade old-profile result. Use `explicit_old_record_results.json` for that acceptance claim.
