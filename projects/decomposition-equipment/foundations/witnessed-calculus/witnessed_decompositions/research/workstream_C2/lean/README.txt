C2 OPTIONAL LEAN SLICE -- ACTUAL GENERIC PUBLIC CALCULI

Frozen contract: v0.1, SHA256
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e
Cleared target: SHA256
b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4
Full C2 remains OPEN pending D2/E use. This source does not implement or accept
D2, any equipment universal property, or C3. Standard infrastructure; no novelty
claim. The independent review and parent acceptance are separate from authorship.

WHAT IS KERNEL-CHECKED

RelationInterface.lean constructs two actual public
WitnessedDecompositions.Calc values, not a parallel private calculus record:
  containmentCalc: C(profile) is contained in the independently supplied whole;
  exactCalc: C(profile) equals that whole;
and exactInclusion: a strict Calc.Hom from exactCalc to containmentCalc.
Strict means literal structure preservation, not universal properness.

The interface wrapper Interface I X has exactly one field, label:I. Projection
and constructor are inverse, so it changes no interface information. Its quiver
edges are ALL predicates X(i) -> X(j) -> Prop, i.e. binary relations. X may be
any family of carrier types, including empty types; all finite-set families in
the frozen target are therefore included. No Fintype, DecidableEq, nonemptiness,
classical choice, bound on arity, or bound on tree depth is assumed.

The wrapper equivalence extends to ALL model data, not just interface labels.
Equip the mathematical label set I with edge family (i,j) |-> predicates on
X_i x X_j. Projection sends a wrapped arrow R:a->b to the identical predicate
at (a.label,b.label); the inverse sends that predicate to the arrow from
Interface.mk i to Interface.mk j. Their inverse laws follow from label(mk i)=i
and mk(a.label)=a, with endpoint equality transport where needed. On components
apply these maps to both endpoints and the retained relation. On paths map nil
to nil and cons to cons with the same predicate; induction on a path proves both
composites identity. The corresponding Slot maps preserve Empty, Sum.inl and
Sum.inr(), so are ordered bijections preserving componentAt and independent
occurrences, even when component relations repeat. Induction also shows evaluate
is unchanged under these maps, since its diagonal and existential-composition
clauses use exactly the same carriers/predicates. Hence they restrict to inverse
maps on both ContainmentOp and ExactOp and on prescribed-profile operation
fibres: transport the path, keep the whole relation and its validity proof.
Expansion commutes with these constructor maps by induction on the outer path;
therefore identity and substitution are preserved. This paragraph is the
explicit P coordinate identification with the unwrapped mathematical model,
not a claim of additional Lean declarations absent from the source.

An operation retains its entire public Quiver.Path and fixed Component output;
only its validity proof is irrelevant. evaluate takes the empty path to equality
and a snoc path to existential relational composition. evaluate_expand_le/eq
supply actual substitution existence. The two units and associativity are fields
of the actual public Calc, using the full public occurrence-indexed expansion
and composeAt_profile law, not just an equation of composite relations.

containmentFiberEquiv and exactFiberEquiv give explicit inverse maps between the
public prescribed-profile operations and their singleton-or-empty conventions.
The two fibre_subsingleton theorems apply only at FIXED profile and output.
They neither collapse total operations with different paths nor identify trees.

primitiveAssignment has the real public Signature.Assignment type and retains
all primitive input/output types. presentationExtension instantiates the real
A2 Tree.extend. presentationExtension_unique is uniqueness among all strict
Calc.Hom maps with those primitive images. same_frontier_same_semantics proves
the intended thin-semantic loss at a fixed whole; it has no conclusion asserting
syntax equality. The independent finite certificate provides actual distinct
primitive/tree examples; this file does not silently add a presentation quotient.

restrictionQuiver is a real quiver map between generally DIFFERENT relation
quivers, induced by one map Y_i -> X_i for each interface label. It is not falsely
typed as a same-base Calc.Hom. restriction_path_comparison covers all arities;
its constructive existential proof sends intermediate values through the maps.
restrictContainment applies that inclusion to the independently restricted whole.
Identity/composite quiver and path restriction laws are checked. The all-positive-
arity equality theorem requires surjectivity only at the targets of prefix edges,
which are exactly the internal interfaces; neither endpoint is constrained.
The nullary kernel formula and diagonal comparison equality IFF injectivity are
separate checked statements. diagonal_containment_nonexact proves permitted
nonexactness whenever a carrier contains two different supplied elements.

EXPLICIT P/L/C BOUNDARY

L: exactly the declarations in RelationInterface.lean and AxiomAudit.lean,
including actual generic Calc and A2 extension, the global-family restrictions
above, and the full positive-path sufficient equality statement.
P: the full arbitrary occurrencewise-map convention, explicit maps between
realization SETS (not just existential propositions), incidence-compatible forest
restriction/substitution commutation, and its comparison with the finite code
are in ../proof/C2_Model_Theorem.md. In particular no Lean theorem claiming
restriction/substitution commutation for inconsistent nullary boundary maps is
present. Nullary contractions require agreement of both primed boundary sets
and maps. The generic calculus proof is L but the full restriction-forest package
remains P. D2's sharp necessity classification is not claimed anywhere here.
C: exhaustive and named finite certificates are Python execution, independently
checked elsewhere, not kernel computation in this module. There is no native_decide
or code-generation oracle in the source.

TRUST AND BUILD

All 40 audited definitions/theorems have actual dependency closures contained in
{propext, Quot.sound}. Some have no axioms. Classical.choice, sorryAx, admissions,
custom axioms, and native computation do not occur in their closures. Quot.sound
supports Lean's ordinary function extensionality machinery; this is not an
axiom-free claim and not a quotient of syntax by all semantic equalities.
AxiomAudit.log and AxiomReport.json preserve the exact per-declaration result.

Use the project's unchanged pinned lean-toolchain/lake-manifest.json. From its
root with Lean/Lake on PATH and pinned dependencies installed:
  lake build WitnessedDecompositions.FreeExtension
  mkdir -p .lake/build/lib/lean/research/workstream_C2/lean
  lake env lean -o .lake/build/lib/lean/research/workstream_C2/lean/RelationInterface.olean research/workstream_C2/lean/RelationInterface.lean
  lake env lean research/workstream_C2/lean/AxiomAudit.lean

These are author verification commands. Independent reproduction must compile
project sources in a fresh output/checkpoint, as the parent/reviewer driver does;
the commands alone do not claim a clean rebuild of all Lean/mathlib foundations.
DependencySnapshot.json records all local transitive source imports and hashes.
No baseline source file was modified. .olean files are disposable build outputs,
not source artifacts or mathematical acceptance evidence by themselves.

ORDINARY ELABORATION REPAIRS, NO TARGET WEAKENING

attempt01: final evaluate_expand_eq goal needed an explicit definitional rfl.
attempt02: generic containment/exact Calc and strict inclusion compiled.
attempt03: two rewrites of entire quiver maps produced dependent-motive errors;
           replaced by direct applications of the existing mapPath laws.
attempt04: freeCalc needed the public Tree.freeCalc namespace qualifier.
attempt05: A2 extension, semantic collapse, restriction package compiled.
attempt06: added all-positive-path internal-surjection theorem; compiled.
attempt07: anonymous '_' binder was invalid syntax in a subtype; named it.
attempt08: entire module and axiom audit passed, with two unused binder warnings.
attempt09: renamed those binders _u; warning-free module and audit pass.

All nine logs are retained. They are author development history, not independent
reviews, counterexample-based target amendments, or concealed proof admissions.
