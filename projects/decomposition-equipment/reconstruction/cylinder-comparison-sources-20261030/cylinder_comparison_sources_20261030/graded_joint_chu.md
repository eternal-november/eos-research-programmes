# Minimal graded joint-context closure and two-sided comparison

Status: proved elementary theorem in Set/K pairing semantics, combining known Chu functoriality and resource indexing. Not an arbitrary-CFS theorem, not a finite-data reconstruction oracle, and not a novelty claim.

## 1. Declare the admitted syntax and build the least closure

Let profiles Γ be actual joint interfaces; a preparation at Γ is a joint fragment, not a tuple of marginal preparations. Specify seed preparations/tests, a typed collection of wiring generators, and the allowed finite gluing operations. Assign nonnegative integer costs to seeds and positive costs to substantive primitive nodes; structural identities can have zero cost. Costs add on gluing. If equations identify diagrams, require them to preserve the resource charge, or retain a charged derivation along with its underlying diagram.

Construct fragments by finite derivation trees from these seeds and operations. Equivalently, start with seed sets and repeatedly add every well-typed gluing of existing fragments, retaining its cost. This is the least family closed under the declared rules: induction on derivations shows it is contained in every such family. For budget B, discard derivations of cost >B. Nonnegative costs ensure no discarded derivation can later generate a ≤B fragment. This produces P_Γ^{≤a} and T_Γ^{≤b}.

If a residual requires filling all but one boundary of a multi-boundary generator, include exactly that finite-gluing rule and charge the generator plus all filled fragments. The resulting open fragment is added to the corresponding preparation/test family. Thus residual closure is generated, not assumed. Any auxiliary component required by a residual is explicitly recorded in its derivation and resource charge. Correlated joint seeds are retained as joint seeds. Independent juxtaposition may be one admitted rule, but does not exhaust joint fragments.

A wiring diagram w:Γ→Δ of charged cost c induces actual syntactic maps

    w_!:P_Γ^{≤a}→P_Δ^{≤a+c},       p↦w glued after p,
    w*:T_Δ^{≤b}→T_Γ^{≤b+c},       t↦t glued after w.

They preserve the declared diagram equations and satisfy (v w)_!=v_!w_! and (v w)*=w*v*. No hidden-state representation or full pre-existing model grammar is required for this syntactic construction.

## 2. Semantic input and derived cut law

Let Eval assign values in K to the closed diagrams under consideration, invariant under the admitted gluing equations. It may be supplied by a verified primitive semantics, direct observations, or a partially filled experimental ledger. The exact theorem initially concerns a total, correct Eval on its specified finite or infinite domain. It does NOT infer such values from the seed tables.

Set E_Γ(p,t)=Eval(t glued to p). By associativity, both sides of

    E_Δ(w_!p,t)=E_Γ(p,w*t)

are evaluation of the identical closed diagram t w p. Thus the cut identity is derived; it is not an assumption that reconstruction preserves wiring. The closure construction explicitly lists the additional closed experiments required to instantiate the theorem.

## 3. Exact fixed-total-budget theorem

Fix B∈N. Define a category G_B whose objects are (Γ,a), 0≤a≤B. A morphism (Γ,a)→(Δ,a+c) is an admitted wiring w:Γ→Δ with charged cost c and a+c≤B. Compose using diagram composition and addition of charges.

Define the pairing

    A_B(Γ,a)=(P_Γ^{≤a}, T_Γ^{≤B−a}, E_Γ).

A morphism w gives an ordinary Chu arrow

    (w_!,w*): A_B(Γ,a)→A_B(Δ,a+c).

Indeed its forward map has the required preparation domain/codomain, while its backward map takes tests of cost ≤B−a−c into tests of cost ≤B−a. Section 2 supplies Chu adjointness. Therefore A_B:G_B→Chu(Set,K) is a functor.

Let Q:Chu(Set,K)→chu(Set,K) be biextensional collapse (quotient equal rows and equal columns). Then

    Q A_B:G_B→chu(Set,K)

is the reconstructed, budget-correct functor. In expanded notation, the descended comparison is

    Q(P_Γ^{≤a},T_Γ^{≤b+c})
       --Q(w_!,w*)-->
    Q(P_Δ^{≤a+c},T_Δ^{≤b}),       a+b+c=B.

**Direct proof of descent.** Equal source rows agree against every w*t because its cost is ≤b+c, so their pushed preparations have equal target rows. Equal target columns agree against every w_!p because its cost is ≤a+c, so their pulled tests have equal source columns. This proves both components descend, rather than assuming it.

**Cut coherence.** For w of cost c and v of cost d, use source split (a,B−a), intermediate split (a+c,B−a−c), and target split (a+c+d,B−a−c−d). The quotient components of Q(vw) and Q(v)Q(w) agree on representatives, hence agree everywhere. Identity and all declared cost-preserving diagram equations descend similarly.

The two-sided quotient comparison itself is a vertical double-Chu cell, as in the ungraded note; an ordinary Chu arrow from every unreduced object to its simultaneous two-sided quotient would have the wrong negative variance. The reconstructed wiring arrows ARE ordinary Chu arrows.

## 4. What 'minimal' and 'finite' mean here

Minimality is relative to the declared seed fragments, admitted operations, equations and resource convention. It is syntactic least closure, not a claim to discover all physically possible interactions or the globally smallest experimental basis.

Finite enumeration follows, for example, from finitely many relevant profiles/port labels, finitely many seeds and generators, bounded arity, positive node costs, and a finite bound on derivation size. Zero-cost cycles, unrestricted zero-cost disjoint closed components, infinitely many parameter values or unrestricted profile growth can destroy finiteness. They must be normalized away, bounded, or represented symbolically. Even finite syntax does not make Eval computable or measured.

An exact reduced pairing at a given budget requires enough evaluation information to certify its row/column equivalences. If some entries are unknown, keep them marked unknown in an experimental ledger; do not replace every unknown by one extra outcome and collapse those equal placeholders. One sound specification is equivalence under ALL semantic completions compatible with known observations and admitted equations, but checking this can itself be hard. The closure algorithm produces required experiments and comparison obligations, not their answers.

## 5. Quantitative cut residuals

Let K carry a metric d. An approximate arrow (f,g):A→B has cut residual ≤ε when

    sup_(p,t) d(E_B(fp,t),E_A(p,gt)) ≤ ε.

If (h,k):B→C has residual ≤δ, then (hf,gk) has residual ≤ε+δ: insert E_B(fp,ku) between the two endpoint evaluations and use the triangle inequality. All suprema are only over the resource-admissible domains above. Thus residual budgets add along admitted finite cuts, with shifted domains, not from unchanged local certificates. More precisely, if w:Γ→Δ has cost c and v:Δ→Θ cost d, define D(w;a,b) using preparations at Γ of cost ≤a and tests at Δ of cost ≤b. Then

    D(vw;a,b) ≤ D(v;a+c,b)+D(w;a,b+d).

The intermediate evaluation is E_Δ(w_!p,v*t). Each term must be certified on its displayed enlarged preparation/test domain.

Define row pseudometrics d_A^row(p,p')=sup_t d(E_A(p,t),E_A(p',t)), and analogously column pseudometrics. The same triangle inequality gives

    d_B^row(fp,fp') ≤ d_A^row(p,p')+2ε,
    d_A^col(gt,gt') ≤ d_B^col(t,t')+2ε.

For ε=0 this recovers exact two-sided descent/nonexpansiveness with the CORRECT shifted budgets. For ε>0 it does not imply exact quotient descent, and threshold 'distance ≤ε' is not generally transitive. Retain approximate maps, pseudometrics, or explicitly justified clusters instead of pretending to have an equivalence quotient. In particular, one exact source row class may map to several target classes, but their row-metric diameter is ≤2ε. This defines a controlled relation witnessed by the original preparations, not necessarily a function on classes. For composition, keep the SAME intermediate raw witness supplied by the composed syntax. Unrestricted relational/span composition may mix distinct intermediate representatives; any resulting extra discrepancy requires its own diameter/error bound and is not covered by the simple residual sum.

If estimated pairings have uniform errors η_A,η_B against exact pairings and the syntactic residual maps satisfy the exact cut law, their observed cut residual is at most η_A+η_B. These are conditional error certificates; unknown entries provide no such bound. No finite observations imply a bound outside the explicitly covered closure without further assumptions.

## 6. Joint-profile Isbell route and copying caveat

At the purely formal level, assign a category C_Γ to each JOINT profile and let an actual wiring functor W:C_Γ→C_Δ act by I(W):I(C_Γ)→I(C_Δ). Pseudofunctoriality handles successive joint wiring, including specified diagonals/deletions. External product is only a constructor for independent inputs, not an identification of I(C_Γ×C_Δ) with I(C_Γ)×I(C_Δ). Thus intentional correlation is represented rather than ruled out. This uses known Isbell functoriality; it adds no automatic operational semantics.

For stochastic public-port copying, the specified operation is Δ_B∘F. It is generally NOT (F⊗F)∘Δ_A: the latter independently resamples F twice after copying its input. Copy is natural for deterministic maps, not arbitrary stochastic maps. Any comparison must specify which operation and which public/joint boundary are admitted before making a refinement claim.

Only finite cuts and admitted finite guarded-feedback unrollings are covered. No infinite feedback, trace identity, fixed-point convergence or budget-free test extension is inferred.

## 7. Known-status audit

Ordinary biextensional collapse and its functoriality are explicitly known: Hughes, [Intensional Double Glueing, Biextensional Collapse, and the Chu Construction](https://www.entcs.org/files/mfps19/83007.pdf), §2.1.1. The typed/poly/double framework is in Shulman, [The 2-Chu-Dialectica construction](https://arxiv.org/pdf/1806.06082). Additive resource-indexed categorical semantics is established independently, for example [Graded Hoare Logic and its Categorical Semantics](https://arxiv.org/abs/2007.11235). A bounded search did not locate this exact budget-split pairing formula as a named theorem; that does not establish novelty. The mathematical proof here is elementary, and the genuine increment over an ungraded one-sorted contextual congruence is the explicit joint-profile/two-sided budget shift and its cut-coherent comparison, not a new contextual-equivalence principle.
