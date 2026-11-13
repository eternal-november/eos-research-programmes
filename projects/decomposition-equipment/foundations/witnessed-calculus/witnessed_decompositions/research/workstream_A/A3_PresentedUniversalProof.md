# A3 presented universal property: proof and trust boundary

Status: author submission of integrated Lean and mathematical evidence, not acceptance. Canonical contract SHA256 is 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e. Exact frozen quantifiers and nonpassing shortcuts are in A3_TargetFreeze.md. The independent review is separate.

## 1. What is input and what is proved

The arbitrary input is a signature S and a family E(c,p)(t,u) of declared equations on two actual operations in the same full typed profile fibre. No semantic equality, reduction relation, normalization procedure, convergence hypothesis, or recoverability axiom is input.

Presentation.Derives is an inductively generated proposition with exactly these constructors: a declared E instance; reflexivity; symmetry; transitivity; and simultaneous substitution of related outer operations by pointwise related families, each with its prescribed common replacement profile. It does not mention any model, quotient, or operation-count invariant. Thus its definition cannot silently identify all equal images in a selected model. Theorem derives_parallel proves preservation of the complete frontier by induction on those derivations. Theorem derives_least, also by induction, proves that every other parallel substitution congruence containing E contains Derives. This establishes the least congruence rather than assuming it.

ParallelCongruence is a generic *input interface* for quotient construction: it specifies an equivalence relation, parallelism and substitution stability. These are not assumed of the presentation. Presentation.congruence constructs the required instance from the preceding independently proved derivation rules. A strict map's kernel is another proved instance, used to derive soundness, but is never substituted for the generated relation.

## 2. The actual quotient and substitution descent

For any proven ParallelCongruence R on any Calc M, QuotientCalculus.lean defines the output-indexed operation space as Quotient(R.setoid c). The profile is a Quotient.lift, justified by R.parallel, so quotient equality cannot change intermediate interfaces, edges, or order. Representatives of a prescribed quotient fibre are original operations in exactly that fibre, not arbitrary operations whose profiles are forgotten.

The implementation uses Quotient.out to choose representatives. This is noncomputable and introduces the standard Classical.choice axiom. It asserts no canonical form, terminating rewrite process, or decision procedure. The quotient-substitution independence theorem proves that replacing the outer representative and every inner representative by congruent ones leaves the resulting quotient operation unchanged. Its proof uses the proven substitution-stability field of R and Quotient.sound. Therefore representative choice is an implementation device, not a disguised quotient law.

Actual quotient identities and substitution are then defined. Both units and the exact CalcData.composeFamily associativity law are proved by lifting arbitrary operations and whole occurrence-indexed families along the surjective projection, applying the source calculus laws, and using canonical profile/occurrence transport. No quotient law is a new axiom. The strict projection theorem proves preservation of all supplied-profile substitutions. The quotient_eq_iff theorem uses the ordinary quotient soundness/exactness theorem to identify equality with R.Rel.

For R=Presentation.congruence E this produces Presentation.quotient E and Presentation.projection E. Their equality test is *propositional* derivability, not an algorithm deciding it.

## 3. Factorization and the presented hom correspondence

Let M be any target calculus in any independent operation universe, and a any typed primitive assignment satisfying every declared E instance. A2 constructs the unique free strict extension. Presentation.sound proves, using derives_least and the kernel of that free extension, that it respects every generated derivation. The generic quotient factor construction descends the operation map by Quotient.lift; strict identity and substitution preservation are proved, not carried as hypotheses about the factor. Projection followed by factor equals the free extension on every operation.

Any two strict quotient maps with the same projection composite are equal: every quotient operation is the image of an original operation, and equality follows pointwise, then by strict-morphism extensionality. Consequently the factor is unique among all strict quotient maps.

Conversely a strict map from Presentation.quotient E to M gives a primitive assignment by composing with projection and restricting to generators. It satisfies E because each declared pair is related by the equation constructor and therefore equal after projection. The actual Lean maps Presentation.extend and Presentation.restrict are inverse (extend_restrict and restrict_extend). Presentation.homEquiv is the displayed bijection between strict quotient maps and Model E M, the type of typed assignments satisfying E. Its target naturality is proved as extend_natural using the free target-naturality theorem and projection uniqueness. No uniqueness theorem is restricted to functions that were already assumed to obey a recursive node equation.

## 4. Derivability, quotient equality, and all models

Soundness into an arbitrary target universe is Presentation.sound. For completeness, the universe in EqualInAllModels is explicitly max(u,v,w), large enough to contain the actual presented quotient on S. The canonicalModel is the quotient's projected generator assignment; restrict_satisfies proves it satisfies E. Interpreting a raw tree in this model is precisely projection, by interpret_canonical. If t and u agree in every model in this stated class, they therefore agree in the canonical model; quotient_eq_iff gives a derivation. The converse is soundness.

Thus derives_iff_all_models and quotient_eq_iff_all_models prove the required equivalences, with the model-universe quantifier visible. Restricting to a small selected model family not containing the quotient would not justify the reverse implication. The separately cross-universe soundness theorem covers arbitrary larger target universes as well. No claim is made that equality in one chosen relational or statistical semantics entails derivability.

## 5. Independently described mixed-interface model and separation

PresentationExamples.Mixed extends the original four-interface finite signature by two primitive unary witnesses red and blue on the whole component 0→3. The only declaration is the parallel three-leaf binary regrouping

    cut12_3(split12(a,b),c) = cut1_23(a,split23(b,c)).

The input path is exactly a:0→1, b:1→2, c:2→3 and the common output is whole:0→3. The code proves the two raw trees distinct. The declaration does not mention red or blue and cannot be a nonparallel relation by its indexed constructor type.

Here is a concrete semantics independent of both Derives and the quotient. Instantiate the already proved relational calculus of relational/RelationalTargetProof.md with X(c)=Bool for every component. Assign to all four binary cut witnesses the graph of Boolean XOR, to red the identity relation, and to blue the graph of Boolean complement. Every relation has exactly the declared typed input/output boundary; giving all component carriers the same underlying set does not identify the component indices or their positions. In this model the left grouping maps (x,y,z) to (x XOR y) XOR z, while the right maps it to x XOR (y XOR z). Both equal parity of the three bits, so the sole E instance holds. At input 0, the red corolla outputs 0 and the blue corolla outputs 1. This is a model satisfying E and separating the undeclared parallel equation red=blue. It is not the canonical quotient or a kernel chosen to define E.

In Lean there is an additional independent statistic separator. Tree.weight is defined recursively as the sum of supplied primitive weights. weight_profileGraft and weight_substituteOperation prove occurrence-wise additivity. Give red weight 1 and every other generator weight 0. The declared grouping equation has weight 0 on both sides; derives_weight proves the whole generated relation preserves weight. Consequently undeclared_not_derivable holds. The statisticModel separately quotients by equality of the full profile *and red count*, a previously proved parallel congruence. Its satisfaction and separation theorems are checked, as are the distinct quotient images in the actual presented calculus. This model is evidence, not the definition of Derives.

The Nullary examples use the existing repeated-component signature with no declared equations. They prove its generated relation implies literal tree equality, that the nullary witness is still not an identity, and that projection preserves an actual nullary insertion beside a separate occurrence of the same component. Wrong-profile and wrong-output equation attempts are rejected at typechecking. These tests complement rather than replace the arbitrary-schema quotient theorem.

## 6. Classification, failure evidence, and remaining scope

This is standard free/presented multicategory algebra, implemented with the retained typed occurrence data. It is infrastructure, not an independent novelty or large scientific-contribution claim. Core closure, quotient substitution, factorization and all-model statements are L; the independently described Boolean relational model is P, using a previously reviewed uniform model construction. The code also supplies an L statistic model and separation proof.

The standard axiom closure for generic quotient and its presented consequences includes propext, Quot.sound and Classical.choice. The earlier A1/A2 core audits retain their narrower set. No custom calculus axiom, placeholder proof or native computation is used. No normalizer for arbitrary E is asserted. A4's particular termination/confluence/completeness theorem is a distinct result and must be connected explicitly to this quotient rather than silently treated as part of its definition.
