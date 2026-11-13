# Independent E4 finite-check replay and scope inspection

**Outcome: PASS, 31 October 2026.** A separate reviewer copied only the five
manifest-declared finite sources and the manifest into a fresh independent tree,
verified every SHA-256 pin, ran both supported entry points, and compared the exact
receipt bytes with the verifier's frozen final receipts. Both were identical.
Original and copied finite sources were hash-checked again after execution.
No historical source was edited, no prior mutation result was reused, and no file
was uploaded. Disposable guard mutations remained outside this review package.

## What was actually replayed

- Normal, `-O`, and `-OO` semantic baselines: PASS with byte-identical JSON.
- Ten actual semantic mutations in each of those three modes: 30 expected,
  deterministic rejections, with no uncaught traceback accepted as a rejection.
- 55 source/output/interpreter controls: PASS. These include source/dependency
  drift, manifest shape/schema, symlinks, output hard-link aliases, protected
  historical paths, falsely claimed modes, and a complete inherited
  `PYTHONOPTIMIZE=2` replay that resets the child optimization modes.
- Every independent finite receipt and guard receipt is byte-identical both to
  its captured stdout and to the verifier's frozen final counterpart.

This is independent **replay and source inspection**, not a separately authored
implementation or a mechanized proof of the uniform mathematical theorem.

## Actual semantic content inspected

`Forest` retains the input/output graph words and each output root's ordered
partition. Composition substitutes the stored cuts and retains root allocations,
including empty occurrences; it is not normalization to a flattened graph name.
`WC` retains the full source path, source interface, outside boundary functions,
forest, endpoint-compatible finite function on the actual compatible tuple span,
and one global scalar. Scalar equality is independent of the coefficient data.

`composite` builds an actual tuple-span apex and actual universal cell. `factor`
expands the stored substring tuple and applies the inverse chosen scalar weight.
The finite suite enumerates whole cell fibres for its tested contexts, including
two-sided contexts, nullaries, singletons and noninjective outside boundaries;
three choices use genuinely different tagged/reordered apexes and scalar weights.
It checks surjectivity and injectivity rather than only formal path names.

Associators, unitors and choice comparisons are actual unary cells with explicit
coefficient functions and scalar corrections. The pentagon uses tensor-whiskered
local associators, and the triangle uses actual unitors. There are 3 pentagons,
3 triangles, 24 comparison inverse pairs, and 27 three-choice cocycles. These
finite diagrams are examples of, not a substitute for, the all-finite P proof.

The old-profile tests compare the complete enumerated semantic fibres to the old
`gcells` images for graph sizes 0–3 and arities 1–3, and check scalar nullaries.
The 325 reported checks are executions, not a claim of 325 distinct profiles.
The principal six-vertex data retain both cross-edge wholes, repeated equal
middle edge graphs, opposite occurrence-indexed cuts, global/local scalars,
and 9 actual proper-interval scalar-factor pairs.

## Necessary evidence boundaries

1. The original contract's E4 requirement is at lines 466–482 of the verbatim
   contract. This finite evidence supports concrete examples and regressions;
   the unbounded construction, actual source-syntax nonrepresentability,
   relative category universal property and original-core conservation are P
   obligations reviewed separately. No bounded run establishes those theorems.
2. The graph-word/span/scalar equipment is a separating ordinary semantic model,
   not asserted to be the free envelope itself. The finite two-whole obstruction
   checks graph-coordinate candidates; the P syntax invariant is needed to cover
   every V horizontal term. No backwards preservation of opcartesian cells along
   a merely normal map is used.
3. There is no claimed normal map from the concrete single-graph model S into the
   word model via one-entry words: its old empty-graph unit would not map to the
   genuine empty-word unit. The tests explicitly separate those objects.
4. The finite principal grade realization is the frozen E3 groupoid model with
   3 interfaces and 6 automorphisms at an interface. P §9 now explicitly
   uses this same realization, after the reviewer flagged the earlier literal-
   chain wording. The chain enters only through its faithful path-profile
   realization; the runtime does not test the literal chain category or every
   finite category K.
5. The three finite bad-quotient checks demonstrate explicit collisions under
   whole-, cut-, or scalar-forgetting projections. They do not themselves check
   all functor axioms of an ordinary target; actual bad strong maps and their
   scope are established by P §8.3. The scalar-zero cancellation obstruction
   requires the specified extra universal marking, not merely a new composite.
6. The Rel finite portion checks associativity and units on all relations of a
   two-element set. It is not a direct exhaustive contextual-factor test.
   The graph-free tuple-span regression has 48 cell factors: 16 actual Span
   coefficient maps times 3 auxiliary scalar labels. Its scalar-identity slice
   is the ordinary Span regression. Neither identity regression supplies the
   required genuinely nonrepresentable positive completion class.
7. Full faithfulness on all added V terms, a decision procedure for term-quotient
   equality, arbitrary preservation of preexisting nonnullary exact markings,
   and a new Lean formalization are not certified by these checks.

No finite-check blocker was found. The separate P audit remains responsible for
whether the unbounded arguments discharge the original E4 contract.
