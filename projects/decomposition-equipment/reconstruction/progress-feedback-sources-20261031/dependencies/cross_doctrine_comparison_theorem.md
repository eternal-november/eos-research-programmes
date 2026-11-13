# Cross doctrine reconstruction by coherent comparison spans

30 October 2026. Derived structural theorem and concrete support translation. The free-completion result is an application of Garner's Isbell pseudomonad, not a novelty claim. Native span transport uses the previously proved adequate-CFS rigidity lemma. Native operational minimality is not silently identified with free reconstruction.

## 1. Three distinct comparisons

Let F:C->D be an actual functor between semantic categories. A cylinder r:P=>T consists of its labelled preparation/test diagrams and their actual natural pairing. There are three different questions:

1. Free reconstruction: I(F) R_free,C(r) versus R_free,D(F r).
2. Chosen native CFS reconstruction: F R_C(r) versus R_D(F r), when C,D carry specified cylinder factorisation systems.
3. An operational choice such as minimal normalized stochastic state space versus minimal relational state space. Such choices need not be CFS algebras and need not obey either theorem.

These questions cannot be conflated merely because all constructions are called reconstruction.

## 2. Exact free translation is already general

For small C,D and any F:C->D, the Isbell action is explicitly

 (IF X)+(d)=integral^a D(d,Fa) x X+(a),
 (IF X)-(e)=integral^b D(Fb,e) x X-(b).

The two Set-valued sides are LEFT Kan extensions, with the negative side interpreted contravariantly on arrows of the paired envelope. Their pairing composes the outside arrows with F applied to the original pairing. This is the free CFS-preserving extension of F.

For the canonical free middle of r,

 R_C(r)+=colim_p C(-,Pp),
 R_C(r)-=colim_(t in Tests^op) C(Tt,-).

Kan extension preserves the displayed colimits and takes each representable to the appropriate representable. The induced pairings agree on all generators. Therefore there is a canonical isomorphism

 kappa_F(r): IF R_free,C(r) ~= R_free,D(F r).             (1)

Identity and composite-F laws are Kan-extension Fubini/co-Yoneda laws; their maps agree on generators. Reindexing preparations and tests commutes with these constructions with the actual opposite test variance. There is no assumption here that F preserves a native reconstruction. An alleged support-translation counterexample to (1) would be a mistake.

Since IF preserves E0 and M0, it preserves the adequate mixed pullbacks used by the prior span calculus. Applying IF to the canonical comparison span of any honest realization X yields, after (1), a compatible M-left/E-right span from IF X to the target canonical middle. Target rigidity gives its unique isomorphism to the target comparison. Thus exact free base change transports ACTUAL comparison spans, not merely normalized endpoints.

Primary source: Garner, The Isbell monad, Theorems 3.3, 4.1 and 5.1, https://arxiv.org/abs/1410.7108 . The explicit Kan-extension calculation and mixed-span consequence are derived applications.

## 3. Native theorem with weaker preservation

Suppose C,D have CFSs (E_C,M_C),(E_D,M_D). Suppose their underlying arrow OFSs satisfy the adequate mixed-pullback hypotheses established in the preceding general criterion. This implies the rigidity of compatible M0-left/E0-right normalizer spans. Let F preserve ONLY the underlying arrow classes E0 and M0. It need not preserve E-cocones or M-cones of arbitrary cylinders.

Factor r canonically as

 P --e_C in E_C--> R_C(r) --m_C in M_C--> T.

Applying F supplies an honest target realization X=F R_C(r) of F r, regardless of whether F preserves either full cylinder class. In D, factor its preparation cocone

 F P --a_F in E_D--> G_F(r) --b_F in M_D,0--> F R_C(r).

Orthogonality against the target canonical M-cone gives h_F:G_F(r)->R_D(F r) satisfying

 h_F a_F=e_D,
 m_D h_F=F(m_C)b_F.

Cocone cancellation gives h_F in E_D,0. Define

 beta_F(r)=(F R_C(r) <-[M_D,0] G_F(r) ->[E_D,0] R_D(F r)). (2)

Existence of this one comparison does not require F to preserve any classes. Preservation of the underlying arrow classes is used in transporting and composing such comparisons.

### Composition theorem

For F:C->D and G:D->E preserving their underlying arrow classes, translate (2) by G and compose with beta_G(F r) through its mixed pullback. The resulting span has left M_E,0 and right E_E,0 legs and is compatible with the SAME cylinder GF r. Its left endpoint is GF R_C(r), right endpoint R_E(GF r).

The canonical beta_GF(r) has those same properties. Adequate-CFS rigidity therefore supplies a unique realization-compatible invertible compositor

 beta_GF(r) ~= G(beta_F(r)) ; beta_G(F r).                (3)

Identity and associativity diagrams commute by uniqueness after the canonical mixed-pullback associators. Class-preserving G carries the required mixed pullbacks to mixed pullbacks: its image square is again an adequate mixed square. Thus (3) can be whiskered, not merely compared after forgetting intermediate compositions.

This is a coherent SPAN-valued cross-doctrine reconstruction law. It is not an isomorphism between the native reconstructed objects themselves. It is also not obtained by assuming F preserves full reconstruction.

## 4. Native context-family naturality

Take actual restrictions indexed by B=Prep x Test^op. A B-arrow enlarges preparations and restricts tests, with the corresponding labelled cylinder entries agreeing. For a CFS, canonical-middle context arrows are obtained by the E-cocone/M-cone lifting property using the old preparations and new tests. Identity/composition hold by unique fillers. Preparation enlargement maps are M0; test-restriction maps are E0.

Let X_b be an honest raw realization family with actual context maps. Factor each preparation cocone as a_b:P_b->G_b followed by b_b:G_b->X_b. For a context arrow c:b->b', orthogonality of a_b against b_b' gives the unique G(c) satisfying

 G(c)a_b=a_b' restricted to the old preparations,
 b_b' G(c)=X(c)b_b.

The test equations and the target canonical M-cone show

 h_b' G(c)=R(c)h_b.

Thus the normalizer is ONE natural span X<-G->R in the pointwise mixed-span calculus over B. Apply this construction to X_b=F R_C(r_b). It produces beta_F as a family, and (3) is natural in b because the competing filler maps have the same exterior and cylinder equations.

This retains the signed context variance. It does NOT make simultaneous enlargement of both axes a single covariant arrow, nor repair the previously exhibited failure of ordinary collapsed-span interchange. More general context changes require their actual endpoint/reindexing data; no naturality between unrelated cylinders is presumed.

## 5. Compatibility with honest wiring

Now assume C,D have the declared symmetric monoidal fixed-port wiring doctrines, with chosen duals for the internal wire objects, and that their honest raw assembly operations have the class-preservation already needed by the native wiring theorem. Let F be strong symmetric monoidal and preserve E0/M0. Transport wire duals through F's canonical strong-monoidal duality isomorphisms. Translate the actual joint preparation/test maps, including correlations.

Take X_v=R_C(r_v), the source canonical local carriers. (For arbitrary honest local carriers, first insert their local normalizer spans.) For a finite fixed graph N, source and intermediate target raw carriers are

 A_C(X_v)=(tensor_v X_v) tensor H_C*,
 A_D(FX_v)=(tensor_v FX_v) tensor F(H_C)*.

The strong-monoidal comparison supplies

 alpha_N: F A_C(X_v) ~= A_D(F X_v).                     (4)

Its equality with the preparation/test legs is DERIVED by substituting the monoidal maps in the cup/local-leg/cap formulas. Strong monoidality transports cups, caps, symmetry and their snake equations. Thus the two actual wired cylinders agree up to their supplied endpoint transports. This is not an assumption that native canonical middles commute with F.

Compare the following paths from the translated source raw assembly to the target canonical joint middle:

 F(C^C_raw) ; beta_F(r_N),
 alpha_N ; A_D(beta_F(r_v)) ; C^D_target_raw.             (5)

Here C^C_raw normalizes A_C(R_C(r_v)); C^D_target_raw normalizes A_D(R_D(F r_v)); the intervening A_D(beta_F(r_v)) runs from A_D(F R_C(r_v)) to A_D(R_D(F r_v)). Thus the paths are well typed. Every span in (5) has the required polarities and preserves the SAME joint cylinder. Target rigidity gives a unique invertible comparison between the paths. Its compatibility with nested network substitution, F-composition and B-context changes follows by the same uniqueness. The resulting law is jointly coherent in translation, contexts and the declared wiring.

The assembly hypotheses must still be proved for a new wiring doctrine. They are proved in the preceding free-Isbell fixed-port construction by explicit signed formulas and cup/cap calculation. This theorem does not assert that every operational language has such assembly. If C begins merely traced rather than with dual wire objects, the actual translated trace must also be preserved, or its completion/transport compared explicitly. Strong monoidality alone does not preserve an arbitrary extra trace structure.

## 6. Direct native arrows and exactness

If F preserves E-cocones, orthogonality supplies a direct comparison

 F R_C(r) -> R_D(F r).

If F preserves M-cones, it supplies the opposite direct comparison

 R_D(F r) -> F R_C(r).

The maps preserve both labelled legs. If F preserves both full classes, the translated factorisation is already canonical, so the comparison is an isomorphism. These are Garner's colax/lax CFS-algebra morphism conditions, respectively; the direction must be read from the displayed arrows, not guessed from naming conventions. The maps are coherent by the same lifting uniqueness.

Without those full class conditions the span (2) remains available under the weaker compositional theorem. Failure of full-class preservation does not logically imply that a particular cylinder's comparison is noninvertible; exactness can hold for that specific cylinder. Conversely, arbitrary chosen maps between raw carriers do not become canonical merely because some map exists.

### Local exactness criterion (no global preservation requirement)

For a particular cylinder r, BOTH legs b_F and h_F of beta_F(r) are invertible if and only if the translated chosen factorization (F e_C,F m_C) is in the target cylinder classes (E_D,M_D). This criterion is local to the actual cylinder, not a demand that F preserve every cocone or cone.

Proof. If both legs are invertible, F e_C=b_F a_F belongs to E_D and F m_C=m_D h_F b_F^{-1} belongs to M_D by stability under isomorphism. Conversely, if (F e_C,F m_C) belongs to (E_D,M_D), target canonical-factorization uniqueness gives a leg-preserving isomorphism F R_C(r)~=R_D(Fr). Since F e_C is E_D, the (E_D,M_D,0) preparation factorization F e_C=b_F a_F is isomorphic to F e_C followed by identity; hence b_F is invertible. The canonical isomorphism composed with b_F satisfies the defining equations for h_F, so uniqueness makes h_F invertible as well. QED.

Thus global full-CFS preservation is sufficient for exactness uniformly, but is not necessary for any selected family of cylinders. One may test the actual translated preparation cocone and test cone instead. In particular, replacing the compatibility task by a global lifting requirement would be strictly stronger than this result requires.

### Strictly weaker preservation example

I(1) is Set x Set^op, with unique pairing. Its underlying E0 arrows are those with invertible positive component, and M0 those with invertible negative component. The endofunctor

 H(P,Q)=(P x P,Q x Q)

preserves both underlying classes and is strong monoidal for the componentwise product tensor. It does not preserve general positive or negative colimits and hence does not preserve the full CFS classes.

Take a cylinder with two unit preparations and two unit tests. Its canonical middle is R=(2,2). The translated primitive unit objects are still units, so R(Hr)=(2,2), whereas H(R)=(4,4). The comparison span has apex (2,4): its left positive map and right negative map are the two diagonal maps 2->4. Neither leg is invertible. This demonstrates that (3) is genuinely weaker than exact native reconstruction.

All scalar observations in this terminal-base example are trivial. It proves FORMAL strictness, not a mission-level information loss or a new physical counterexample.

## 7. Concrete translation of nonnegative matrices to relations

Let Mat_+ have finite sets as objects and finite nonnegative-real matrices as arrows, with ordinary matrix composition and Kronecker tensor. Let Rel_fin be finite sets and relations. Define

 supp(M)(x,y) iff M(y,x)>0.

No cancellation and no zero divisors in nonnegative reals give

 supp(NM)=supp(N) compose supp(M),
 supp(M tensor N)=supp(M) tensor supp(N).

Identities, symmetries, deterministic copy/discard maps, cups and caps are preserved. The finite compact trace is also preserved: a traced entry is a finite sum of nonnegative entries, positive exactly when some internal index supplies a related witness.

Hence supp is a strong symmetric monoidal compact functor. The preceding FREE theorem applies with F=supp, and I(supp) transports the reconstruction and raw comparison spans exactly. For finite causal stochastic circuits, supp also records exactly which finite outcomes have positive probability. A copied random source stays one shared source in the relational circuit. Replacing a joint source by the independent product of its marginal supports is a different, generally invalid operation; it is not a counterexample to this functor.

Finite stochastic maps land in total relations, but normalized stochastic maps are not themselves a compact category. The nonnegative-matrix ambient cups/caps are proof structure, not new executable stochastic operations.

## 8. What support loses and what it does not

Support does not retain numerical risk thresholds. It does exactly retain positive-probability reachability and zero-probability exclusion for finite scenarios under the stated full-source semantics. Do not manufacture a raw wiring failure from probability erasure.

For operational/minimal reconstruction, consider two preparations with output columns (1/3,2/3) and (2/3,1/3). Their normalized stochastic matrix has ordinary/nonnegative rank two, so no one-state normalized stochastic realization can reproduce both columns. Its support matrix is all ones and has a one-state relational realization. Thus minimal-state reconstruction can shrink after translation even though free Isbell reconstruction satisfies (1). A deterministic collapse of the two hidden preparation states to one preserves the support cylinder; it cannot preserve their distinct numerical probability cylinder. This example is about operational minimality, not a claimed native CFS on finite stochastic maps.

Feedback admission is separate. The following compact-trace example is only an illustration of a numerical guard, not the core physical-feedback result. As an explicit normalization guard, admit a finite nonnegative feedback result only if the resulting column sums are one. The stochastic two-state matrix

 P_a = [[a,1-a],[1-a,a]],  0<a<1,

has full support for every a. Its compact closed trace is the scalar 2a: normalized only when a=1/2. The relational closed trace is true for every such a. Thus support cannot reflect this numerical admission guard, although it preserves the completed trace itself. This is a stated operational guard example, not an assertion that normalized stochastic maps with this domain form a Haghverdi-Scott partially traced category. Physical feedback must use its actual operational admission law.

For the concrete operational feedback result, see [qualitative_divergence_translation.md](../../cross-doctrine-sources-20261030/qualitative_divergence_translation.md): in the finite substochastic setting, support plus per-input deficit repairs admission for direct-sum first-exit execution, preserving and reflecting normalization. This is a different trace doctrine from compact feedback; the result is finite-only and supplies no section selecting stochastic realizations.

## 9. Scope

There is a genuine cross-doctrine theorem here: coherent span-valued native reconstruction transport under underlying-class preservation, together with its context/wiring law and an exact free-envelope specialization. The preservation hypotheses are weaker than preserving canonical reconstruction and are directly checked for the free lift. The matrix-support functor's composition and finite trace preservation are derived from positivity.

The result does not establish arbitrary heterogeneous institutions, unrestricted feedback, automatic positive/finite native realizations, or general acquisition. New operational doctrines still need an honest assembly proof and their own admission transport. The prior assumption-challenging work is not silently marked complete. Most ingredients are established CFS, adequate-span and monoidal machinery; no priority claim is made.
