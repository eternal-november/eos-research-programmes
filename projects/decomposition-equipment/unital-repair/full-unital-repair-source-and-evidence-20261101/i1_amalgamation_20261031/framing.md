# I1 conservative modular amalgamation — pre-proof scope and acceptance frame

31 October 2026. **Framing, not a theorem discharge or ledger amendment.** User authorized the proposed I1 workstream; this does not adopt the entire revised contract. The target retains original v0.1 I1 lines 622–637, including both conservative inputs, nontrivial shared interfaces, complete mixed refinement coherence, separate cut/interface hypotheses, constructive comparison, and positive and negative families. Use RC0.2's explicit syntax/semantics/laws/boundary and pre-proof scope discipline without converting its additional operational obligations into this task.

## 1. Frozen input class and relation to previous work

Let P be the original ordered graph-cut calculus at arbitrary finite graph bound N and arbitrary finite interface category K, with old commutative scalar specialized to the terminal monoid. All full ordered profiles, actual retained whole graphs, actual partitions, intermediate interface objects/arrows, and repeated occurrence positions remain. Profiles, arity, refinement depth and equation histories are not bounded. For each fixed N,K the old finite presentation uses its actual binary cuts and designated nullaries, not a generator for every semantic operation.

For a finite monoid D, use the active-nonempty-input-edge extension P[D] proved in I5 `model_and_core_comparison.md`: an operation is (g,(d_i)); substitution labels each nonempty final input (i,j) by d_i e_ij. Empty occurrences are retained but receive no coefficient. Generators [d]_H are unary at nonempty H; their multiplication/unit rules and diagonal movement across OLD generators present this extension. This is neither replacing the old global commutative scalar by a noncommutative one nor adding symmetry to the planar calculus.

Positive class: two inputs P[A],P[B] share P via their all-unit inclusions. P is nontrivial: common graph operations, partitions, cuts, nonidentity interface arrows and structural transports are shared literally. The six-vertex repeated-occurrence old example must be instantiated, with a category containing 0→1→2, to demonstrate this. The coefficient data are not a disconnected toy: parent coefficients act on every nonempty descendant; mixed laws and action prefixes consequently enter every refined cut equation. The family is indexed by all N,K and finite coefficient tables.

The bare pushout is the union of the two relative presentations over the common old presentation. The proposed mixed law gives a **comparison quotient of that pushout**, universal among cocones satisfying those mixed equations. Do not call that quotient the bare pushout. Prove its comparison universal property syntactically, including all full profiles. Bare-pushout failure is a separate family below.

## 2. Positive coefficient law, finite criterion, and required proof

Input a table λ:B×A→A×B. With λ(b,a)=(a',b'), impose B_b A_a→A_a' B_b', besides same-channel multiplication and unit deletion. Required finite equations are the two units and two overlaps:

- λ(1,a)=(a,1), λ(b,1)=(1,b).
- BAA: if λ(b,a)=(u,v), λ(v,c)=(w,z), then λ(b,ac)=(uw,z).
- BBA: if λ(c,a)=(u,v), λ(b,u)=(w,z), then λ(bc,a)=(w,zv).

These equations are necessary and sufficient for the specific unit/multiplication/sorting system to have unique A-then-B normal forms without identifying distinct A×B pairs. Prove termination by word length followed by BA inversion count (unit-normalized letters); prove exhaustion of AAA,BBB,BAA,BBA and unit peaks. Product on A×B is (a,b)(c,d)=(a u,v d) for λ(b,c)=(u,v). The pair injections are faithful even if neither projection is a homomorphism. The intersection of their images is the unit, hence the graph-theory intersection is exactly P. This is an operation-equation conservativity statement; it alone says nothing about fullness on cuts.

Required noncommuting positive family: A=C_n, B=C_2, λ(s,a^j)=(a^(−j),s), all n≥3. Product is (a,b)(c,d)=(a α_b(c),bd). The n=3/nonidentity shared graph case supplies an explicit mixed calculation; n remains unbounded. The standard distributive-law/matched-product construction is baseline, not the extra scientific claim.

## 3. Complete refinement coherence — acceptance burden, not an inference from confluence

Pin old `THEOREM.md` and `Completion_Comparison.md` at the I5 copies and hashes recorded in `model_and_core_comparison.md` §7. Old completion compares full normal occurrence-forest tuples. It is not an assertion about new coefficient or mixed-channel paths.

New certificate language must specify objects, actual graft edges, oriented equation edges and inverses, ordinary critical 2-cells, disjoint-redex/variable-overlap squares, and equation/graft naturality (MOut and MIn analogues). A proof of object normal forms is insufficient to establish equality of proof paths. The new diagonal equation duplicates a coefficient symbol but does NOT duplicate frontier variables; distinguish these carefully when proving graft naturality.

Required complete mixed list: BAA/BBA/unit overlaps; mixed sorting versus diagonal movement over each old generator; same-channel multiplication versus diagonal movement; old old critical diagrams with coefficient distribution; independent branches; empty/nullary boundary; mixed equation outside a graft and mixed equation inside an inserted forest. For sorting/distribution, the two paths give the same λ(b,a) on EACH active child, not independently chosen values. Old substitutions and repeated occurrences must remain indexed throughout.

The target comparison is an isomorphism from the explicitly presented refinement completion to the independently defined semantic refinement category of P[A⋈_λB]. Its arrow invariant is the ENTIRE tuple of old normal refinement entries plus each entry's own frontier coefficient array. Equality of final composites, or only root-to-final products after discarding original slots, is explicitly not sufficient. A local certificate transfers only when its source, target, shared graph forest and coefficient constraints align; formulate an iff normal-tuple test and prove completeness by normalizing each retained forest entry, not by defining equality as semantic equality. Any claim of ordinary path coherence needs an actual terminating/coherent normalizer proof or an explicit independently generated path presentation with derived canonical comparison.

## 4. Cut and interface conditions — distinct from conservativity

For a fixed ACTUAL old cut skeleton c, semidirect factorization is the joint system

    x_ij = a_i α_(b_i)(c_ij),     y_ij = b_i d_ij.

The SAME (a_i,b_i) is used for all children j of occurrence i. Thus a B cut record together with an A cut of the source x whose inner labels are t_ij=α_(b_i)(c_ij) determines exactly one joint cut, by c_ij=α_(b_i)^(-1)(t_ij). This is the elementary twisted fibre-product bijection; all iterated trees require accumulated B-prefix actions. Prove it at the actual fixed global source, not just over marginal observations. A coordinate projection to A is generally NOT a calculus morphism.

For quotient/class-wise cut certificates, require exact common skeleton retention and either exact B action records or a proved action-invariance condition on the retained A predicates/classes, plus joint matching of the shared parent factors. Arbitrary independent local quotient matches need not glue. State whether transfer means literal witnesses, existential class signatures, optimal repairs, or multiplicity; these are different. No I5 optimum-reflection argument can simply be copied through a nonhomomorphic A projection.

For cuts of embedded input operations, unrestricted cut fullness is generally false: unit inverses in the omitted group create foreign cuts of a local unit. Claim full transfer only for a declared module-pure factor language, or prove the extra no-foreign-factor condition in the relevant monoids. Preserve and reflect old label-blind existential cut queries separately using unit-internal/leaf-label lifts, not by asserting full fibres coincide.

Structural interface relabelings must retain full profiles and commute with old restrictions. Coefficient transports (f:A→A',g:B→B') require (f×g)λ=λ'(g×f); semidirect form requires f α_b=α'_(g(b)) f. Invertible transports give literal cut/refinement comparison. Noninvertible transports give preservation only unless separate joint lifting/reflection is proved. No arbitrary vertical descent claim is licensed.

## 5. Genuine bare-interface failure family (stronger than a bad added twist)

For every n≥2, define K_n={1,0,x_i : i∈Z/n}, with 1 the identity, 0 absorbing and x_i x_j=0. Define A_n=K_n∪{p}, with p²=p and p x_i=x_i p=x_0, p0=0. Define B_n=C_n∪{0,x_i}, where s^0=1, s^j x_i=x_i s^j=x_(i+j), and all products in the null ideal remain zero. K_n embeds literally in both.

Associativity: A_n is a null ideal acted on by the two-element idempotent monoid {1,p}, whose p-action is the constant retraction to x_0 (and fixes 0). B_n is the same null ideal acted on by the cyclic group via shifts (fixing 0). The left and right actions commute in each local monoid. Products of two ideal elements are zero, so all remaining triple cases vanish. Their multiplication-table presentations are terminating by length and confluent by associativity; both inputs are individually convergent.

In ANY common target identifying K_n, associativity gives

    p(x_i s^j) = p x_(i+j) = x_0,
    (p x_i)s^j = x_0 s^j = x_j.

The raw union of local multiplication-table reductions has the mixed peak p x_0 s^j: left-first reduces to x_j, while right-first reduces to x_0. For j≠0 these are distinct irreducible common letters, so the union itself is not confluent. Hence all n distinct shared elements collapse in BOTH inputs under the generated congruence. No additional mixed relation was imposed. Lift to P[A_n] ← P[K_n] → P[B_n]; the shared theory contains both the nontrivial old graph/interface P and genuine shared coefficients K_n. The unary identity of any nonempty graph exhibits the collapse, and the diagonal law propagates it to nonempty branches of the six-vertex example. This is an unbounded lost-information family (one fibre has size at least n), not repetition of one finite fixture.

Attribution: the basic nonembeddable finite-semigroup mechanism is classical; Jackson, *The embeddability of ring and semigroup amalgams is undecidable*, J. Austral. Math. Soc. 69 (2000), p.273, gives two four-element semigroups sharing a three-element null semigroup, with associativity forcing two shared entries equal. Primary source https://doi.org/10.1017/S1446788700002214. The above n-family and its retained graph/refinement lift need independent verification, and must not be sold as discovering nonamalgamation.

An exact conservative repair preserving BOTH these input monoids and the SAME full interface identification is impossible by the displayed equation. Useful repairs must name what is changed: retain only old P as the common interface (do not alias conflicting x_i), yielding the positive commuting product comparison A_n×B_n with both inputs retained; or modify one local action with explicit permission. If keeping full K_n is mandated, reject composition rather than silently quotient local distinctions. The former repair preserves local inputs and old graph interfaces but deliberately weakens the additional shared-coefficient identification.

## 6. Additional sharp mixed-law boundary and repair

For the cyclic comparison with a^n=1,s²=1,sa=a^r s, the pure A image has order gcd(n,r²−1): derive a=a^(r²), and realize the resulting group as C_d⋊C_2 since r²=1 mod d. Thus the proposed comparison is conservative on A iff r²=1 mod n; B remains faithful via projection. For r=2 and n coprime to 6, A collapses completely with unbounded n. Replacing only the proposed mixed law by inversion keeps both input presentations and their old common P unchanged and repairs the comparison. This is a sharp mixed-law quotient failure, NOT a bare-pushout failure; §5 supplies the latter. Include this only if it helps the accepted boundary rather than distracting from full refinement proof.

## 7. Acceptance evidence and stopping rule

Required paper proofs: constructive pushout/comparison; finite λ iff criterion; both input conservativity; explicitly generated full refinement comparison; twisted joint-cut theorem; separate interface compatibility/reflection; unbounded literal-gluing failure and honest repair. Required finite checks: λ tables and product laws across parameters; nontrivial old graph repeated-occurrence fixture; mixed path negative control; full-tuple-versus-composite negative control; foreign-unit cut negative control; null-ideal failure both inputs; independently replayable audit.

Compare directly with distributive laws/coherent rewriting and structured/decorated cospans. Their constructions supply baseline multiplication or composition frameworks; the extra target is occurrence-sensitive presented-refinement transfer plus exact correlated cut matching over retained graph/interface data, with a checkable failure boundary. Finite scripts test these theorems, do not replace all-parameter proofs. No assertion of full I1 acceptance until independent correctness and original-floor scope review both pass; no unrelated obligation status changes.
