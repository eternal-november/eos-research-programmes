# Cross-doctrine reconstruction: baseline and prior-art notes

Date: 2026-10-30. Research notes; novelty and completion of the broader reconstruction problem are not claimed.

## 1. Decision summary

The support translation is a good concrete *test* of the proposed theorem, but raw finite wiring preservation is already exact. It cannot honestly supply an obstruction to ordinary finite composition, tensor, copying, or compact trace. The substantive question is how the chosen native reconstruction, context regime, and admission of feedback interact with translation. Free Isbell reconstruction by itself is already functorial.

A theorem formulated only as “assume the reconstruction comparison commutes coherently with all operations; then it does” would relocate the target into its hypotheses. Instead: specify source and target reconstruction, calculate the comparison, and derive its operation laws from independently checkable primitive properties. When those properties fail, identify which one actually fails—not a different nearby property.

## 2. Exact support baseline: independent elementary calculation

Let S=R_{≥0}, B={0,1}, addition in B be OR, multiplication AND, and s(x)=1 iff x>0. Then s(0)=0, s(1)=1, s(x+y)=s(x) OR s(y), and s(xy)=s(x) AND s(y). Nonnegativity is essential: there is no cancellation.

For finite matrices, entrywise support defines F:Mat_S→Mat_B=FinRel. In coordinates,

    s((AB)_{ij}) = OR_k (s(A_ik) AND s(B_kj)).

Thus F preserves identities and composition. It also preserves Kronecker tensor, symmetry, transpose, and the zero/one matrices specifying diagonal copying, discarding, cups, and caps. Consequently it is a dagger symmetric compact-monoidal functor (strict on a compatible skeletal convention).

For the compact tensor trace,

    Tr_U(f)_{b,a} = sum_u f_{(b,u),(a,u)},

support is exactly existential quantification over u. Therefore any finite network assembled from those primitives is translated exactly, including closed wires. Interventions represented by replacing a specified component with another matrix are also preserved. No separate generic coherence theorem is needed to establish this particular equality: both interpretations evaluate the same finite algebraic expression through a semiring homomorphism.

This calculation respects an *actual joint matrix*. It does not replace a correlated joint matrix with the tensor of its marginals. Any failure caused by doing that is a modeling error, not failure of support functoriality.

A primary explicit categorical source is Dominic Verdon, *Covariant quantum combinatorics with applications to zero-error communication*, §3.1: its classical motivation identifies Stoch→Rel and Mat_{R≥0}→Rel; Proposition 3.5 develops a quantum counterpart. We need only the classical passage, not the quantum theorem. https://arxiv.org/abs/2302.07776 ; accessible text https://arxiv.org/html/2302.07776 .

## 3. Feedback and stochasticity: actual boundary

FinStoch is a subcategory of Mat_S, but not a compact subcategory with the preceding cups/caps. Compact trace of a stochastic matrix need not be stochastic. For example, take A=B=1, U a two-element set, and f=id_U. Then compact Tr_U(f) is the scalar 2, not the unique stochastic scalar 1. Support gives scalar true, which is a perfectly good relational arrow. Thus exact compact preservation does not prove that the probability-side operation is admissible in FinStoch.

Nor is compact tensor trace the same operation as iterative feedback on a coproduct interface, where a formula such as A+B D* C uses a sum of arbitrarily long internal paths. Admission of that operation requires its own domain, convergence or mass conditions. A strong compact functor does not settle them merely by being compact.

Caution against an attractive but false example: for finite normalized Markov chains, almost-sure eventual absorption is controlled by the support graph (with the relevant exits included). One cannot casually claim that two such chains with exactly the same whole support differ in almost-sure absorption just by changing positive weights. A valid convergence obstruction for arbitrary nonnegative matrices need not remain valid after stochastic normalization constraints are imposed.

The correct reference point for partial versus total trace is Malherbe–Scott–Selinger, *Partially traced categories*: partial trace embeddings and their definedness must be distinguished from existence of a formal trace in a completion. https://arxiv.org/abs/1107.3608 . The independent two-state identity calculation above is sufficient for the present stochastic warning.

## 4. Garner already supplies the free and one-sided comparison machinery

Richard Garner, *The Isbell monad*, establishes the free cylinder-factorisation construction (Theorem 3.3), its pseudoalgebras (Theorem 4.1), and one-sided morphisms (Theorem 5.1). For native reconstruction algebras A:IC→C and B:ID→D, an M-preserving F:C→D has the canonical lax comparison

    B IF ⇒ F A.

An E-preserving F has the reverse colax comparison. Preservation of both gives the invertible algebra comparison. These directions are verified directly in §5, not guessed from the word “lax.” Restricted classes of cylinders are treated in §6. https://arxiv.org/abs/1410.7108 ; https://doi.org/10.1016/j.aim.2015.01.015 ; readable §5 https://arxiv.org/html/1410.7108 .

Implications for this project (our deductions):

* Applying I(F) to the free canonical factorisation is not a novel reconstruction/translation theorem. It is the expected consequence of the free construction.
* “Take support of the reconstructed middle” needs a definition. A general Isbell object is a preparation presheaf, test copresheaf, and pairing—not a finite stochastic matrix. Entrywise support is not already a function on such objects; I(F) is a legitimate, but different and already available, extension.
* Mat_S and FinStoch do not come with an unspecified canonical native full CFS. To use the one-sided theorem substantively, name the native algebras/classes and prove that support preserves the needed class. Stating class preservation without checking it gives a reusable conditional theorem, not the desired concrete result.
* Native small-state, predictive, image, or minimal-rank realizations must not be silently identified with free Isbell middles. They have distinct existence/minimality issues.

## 5. Equipment/base-change prior art and its proper role

Michael Shulman, *Framed bicategories and monoidal fibrations*, supplies the established language for horizontal composites together with vertical changes of base, and for coherent base-change structure via fibrations. Its monoidal and Beck–Chevalley sections are directly relevant if the doctrine-change comparison must also commute with joint wiring or pullback-composed comparison spans. https://arxiv.org/abs/0706.1286 ; published TAC 20(18), 650–738 (2008), https://doi.org/10.70930/tac/2m83wy59 .

Our assessment: a double-category/equipment reformulation may package the coherence cleanly, but introducing such an object is not itself an advance. The work is to prove that the actual reconstruction and semantic translation supply the required cells, and to determine which Beck–Chevalley cells are invertible. If a native functor fails to preserve the mixed pullbacks used to compose comparison spans, expect a directed comparison rather than automatically a pseudofunctor on spans. This is the same boundary expressed by the adequate-CFS comparison-span criterion included in this package.

## 6. Enriched Isbell/Chu prior art—and a crucial doctrine distinction

Lili Shen and Dexue Zhang, *Categories enriched over a quantaloid: Isbell adjunctions and Kan adjunctions*, TAC 28(20), 577–615 (2013), treat distributor-induced Isbell adjunctions and their functoriality with infomorphisms. https://arxiv.org/abs/1307.5625 ; primary journal PDF https://www.kurims.kyoto-u.ac.jp/EMIS/journals/TAC/volumes/28/20/28-20.pdf . This is a baseline against claiming fixed-point/Chu functoriality as new. It is not, by itself, a theorem identifying the Garner CFS construction used here with all enriched fixed-point completions, or proving arbitrary cross-quantale change-of-base preservation.

The important distinction is between a semiring and a quantale. Stochastic matrices compose using sum and product. A quantale such as ([0,1],sup,product) composes distributors using sup and product. Those are different numeric semantics, even though support translates both to Boolean composition. The enriched route should not be advertised as a stochastic theorem without a bridge.

An elementary useful test in the max-product quantale: support preserves its scalar residual a⇒b (a=0 gives 1; otherwise min(1,b/a)) and preserves finite meets. Therefore, for finite preparation/test index sets, entrywise support commutes with the corresponding Isbell conjugacy formulas, which are finite meets of scalar residuals. A claimed finite counterexample to that specific assertion needs scrutiny. Infinite meets are different:

    support(inf_n 1/n)=0, while inf_n support(1/n)=1.

This is a real possible obstruction for an infinite-context enriched completion, but it is not a counterexample to finite stochastic wiring. Moreover, preserving conjugacy formulas and obtaining an equivalence of fixed-point categories are different conclusions: lifting objects, fullness, enrichment, and chosen contexts must still be checked.

## 7. Recommended criterion for a non-vacuous next result

A worthwhile concrete theorem should name:

1. The source and target interaction doctrines, their permitted contexts, and actual joint assembly operations.
2. The reconstruction in each doctrine—not just a common free completion called by two names.
3. The semantic translation F and its derived comparison cell, with its direction fixed.
4. Independently checkable preservation conditions on preparations/tests, factorisation classes, or a verified base-change mate.
5. The resulting wiring/intervention/gluing coherence; feedback only on its proved admission domain.
6. A positive example and a boundary example that concern these exact hypotheses.

The strongest honest near-term outcome may be a classification of when support commutes with a specified native reconstruction, plus a coherent comparison when it does not. Exact finite wiring should be used as a control case. A weaker but useful outcome is to establish that the proposed support example contains no obstruction at the level currently being modeled, thereby preventing another misframed contract.

Novelty status: not established. The general packaging sits close to known Isbell algebra morphisms, framed-category base change, and enriched Chu functoriality. The candidate new contribution must reside in derived cross-doctrine reconstruction/admission comparisons or a concrete sharp obstruction, rather than the bare existence of those formalisms.

## 8. Extension: direct-sum first-exit feedback (verified primary baseline)

This is the operationally relevant feedback example, distinct from compact tensor trace.

**Primary baseline.** Pablo Andrés-Martínez, *Unbounded loops in quantum programs: categories and weak while loops* (2022), Definition 3.2.15 and Proposition 3.2.16 with the following discussion, printed pp.111–113, establishes that finite SubStoch with disjoint union/direct sum and the execution formula is **totally traced**. Its restriction to Stoch is a **partial trace**, admitted exactly when execution yields a stochastic matrix. The proof uses the strong summation structure, singleton elimination, and vanishing II. https://arxiv.org/abs/2212.05371 ; primary institutional PDF https://era.ed.ac.uk/bitstream/handle/1842/39696/Andr%C3%A9s-Mart%C3%ADnezP_2022.pdf?sequence=1 .

For the target, finite relations with disjoint union have the standard finite-path trace. See Miklós Bartha, *On the completeness of the traced monoidal category axioms in (Rel,+)*, Acta Cybernetica 23(1),327–347 (2017), https://doi.org/10.14232/actacyb.23.1.2017.18 . Earlier standard execution-formula machinery appears in Haghverdi–Scott, *From Geometry of Interaction to Denotational Semantics*, Proposition 3.4 and Examples 3.5, https://doi.org/10.1016/j.entcs.2004.06.052 .

### Independent concrete proof of convergence and support preservation

Write a finite substochastic kernel f:A+U→B+U in block form [[P,Q],[R,S]], with columns as inputs. Define

    ex_U(f) = P + sum_{n>=0} Q S^n R.

This sums probabilities of finite paths first exiting at B. It is meaningful even when I−S is singular or S has a closed absorbing class. It does NOT require the matrix series sum S^n itself to converge.

Let 1_X denote the all-ones row vector. Substochasticity says

    1_B P + 1_U R <= 1_A,
    1_B Q + 1_U S <= 1_U.

For each N, the partial sum satisfies

    1_B(P + sum_{n=0}^N Q S^n R)
      <= 1_B P + 1_U(I−S^(N+1))R
      <= 1_B P + 1_U R <= 1_A.

All summands are nonnegative. Thus monotone entrywise convergence exists and yields a substochastic kernel. This direct calculation agrees with the cited total-trace theorem. The trace axioms have a finite-path interpretation; nonnegative regrouping legitimizes decomposing paths for nested feedback rather than relying on conditionally convergent matrix series.

For any countable family of nonnegative real numbers with finite sum, support(sum_i x_i)=OR_i support(x_i). Applying this entrywise, together with finite matrix multiplication preservation, proves

    support(ex_U(f)) = ex_U(support(f)).

Thus support is an exact traced symmetric monoidal functor from (FinSubStoch,+,ex) to (FinRel,+,finite-path trace). This is a concrete consequence of standard execution semantics and elementary positivity—not a claimed novel theorem. On Stoch it preserves the values of all admitted traces; the target trace being defined does not reflect source admission.

### Actual admission witness

Take A={a}, B={b}, U={u}, and stochastic f with

    a -> .5 b + .5 u,
    u -> u.

Its blocks are P=.5, Q=0, R=.5, S=1. Execution is the substochastic scalar .5. It is therefore defined in FinSubStoch but not admitted as a trace in Stoch. The relational finite-path trace contains a→b and is total as a relation. Hence relational MAY-totality does not reflect probability-one exit. The obstruction is not a failed trace equation: the exact support equation holds.

### MAY, almost-sure, and demonic termination are different predicates

* MAY exit: at least one finite supported path reaches B.
* Almost-sure exit: total first-exit mass is 1.
* Demonic all-path exit: every maximal supported execution exits, with infinite paths counted as nontermination.

The witness above has MAY but not almost-sure exit. Conversely, a→u and u→.5 b+.5 u exits almost surely, yet has the supported infinite path u,u,u,..., so fails demonic all-path termination. Neither relational MAY-totality nor demonic termination should silently be substituted for almost-sure termination.

Important scope limitation: for a finite *stochastic* transition system with its whole support graph retained, almost-sure exit can be checked by excluding reachable closed internal recurrent classes. Thus the witness does not show that the original support graph cannot determine the admission property. It shows that the ordinary relational trace, which hides the internal behavior and retains only finite-path reachability, does not carry that property. For arbitrary substochastic kernels, missing mass additionally matters and is itself not determined by ordinary entrywise support. A richer target must specify which termination/divergence information it retains.

Finally, the earlier compact-trace(id_2)=2 calculation is only a warning against confusing tensor/compact semantics with stochastic control flow. It is not the first-exit feedback obstruction and should not be presented as one.
