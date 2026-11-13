# Lenses and causal representations as apprehension enrichments

Status: `derived` constructions in the strict, total setting specified below; their general algebraic laws are kernel-checked in [ApprehensionEnrichments.lean](ApprehensionEnrichments.lean). The choice of these regimes remains a proposal, not repository acceptance or an identification of all apprehensions with them.

Both constructions fit the existing `Str`, `Closure`, `emb`, `OccursIn` signature. They add semantic data and laws to the legs, with explicit maps forgetting those additions. Moreover, ordinary serial lens and causal-map composition is exactly the existing supported re-grounding formula on a canonical subfamily. Neither construction requires replacing that product. Applying an update or intervention is a separate action available through the enriched data.

This is a construction of concrete enriched models of the base, not a claim that every arbitrary pre-existing `ApprehensionSystem` can be enriched this way. No proof-relevant `SameContent` or higher coherence is modeled here. Laws are equality propositions in Lean; their proofs are irrelevant to equality, while update policies, context maps, intervention maps, and chosen support arrows remain data.

## One explicit base and its enriched fibres

Fix an object type \(O\) and a carrier \(|B|\) for each \(B:O\). Instantiate the existing fields by

\[
\begin{aligned}
\operatorname{Str}&=O,\\
\operatorname{Closure}(B)&=\sum_{X:O}(|B|\to|X|),\\
\operatorname{emb}(X,d)&=X,\\
\operatorname{OccursIn}(X,A)&=(|A|\to|X|).
\end{aligned}
\]

Thus an apprehension is precisely

\[
i:A@B=(X,d_i:|B|\to|X|,p_i:|A|\to|X|).
\]

Here an occurrence is realized as a readout into the content carrier. This is a particular allowed instance, not a redefinition of occurrence in the general theory. The two legs retain their different roles although their carrier-level maps have the same mathematical shape. The `RawApp.toBase` and `RawApp.fromBase` definitions are inverse conversions to the original dependent-sum form; both round trips are checked.

The raw derivation unit is \((B,1_{|B|})\); derivation transitivity composes functions. For \(i:A@B\) of content \(X\) and \(j:B@C\) of content \(Y\), take proof-relevant support to be

\[
\operatorname{Supp}_0(i,j)=\sum_{w:|Y|\to|X|}(d_i=w\circ p_j).
\]

Restriction returns \((X,w):\operatorname{Closure}(Y)\), so it preserves the content object literally. The existing formula becomes

\[
\operatorname{comp}_0(i,j,w)=(X,w\circ d_j,p_i).
\]

Now suppose the maps carry an enrichment. Write \(E(B,X)\) for enriched arrows and \(U:E(B,X)\to(|B|\to|X|)\) for forgetting extra data. Once identities and composition of these arrows have been constructed and proved to obey the category laws, with \(U\) preserving them, define

\[
\operatorname{Closure}_E(B)=\sum_X E(B,X),\qquad
\operatorname{OccursIn}_E(X,A)=E(A,X).
\]

An enriched apprehension is again \((X,d_i,p_i)\), with both legs in \(E\). `App.toBase` and `App.fromBase` give checked inverse conversions to this enriched instance of the original dependent sum. Forgetting gives \((X,U(d_i),U(p_i))\): explicit maps on carriers, closures, and occurrences preserving `emb`. This does not assume a previously defined category of apprehension systems. In fibre notation the extra data over a raw reading is

\[
\operatorname{Lift}_E(d_i)\times\operatorname{Lift}_E(p_i),
\qquad
\operatorname{Lift}_E(f)=\sum_{e:E(B,X)}(U(e)=f)
\]

for each appropriately typed leg \(f:|B|\to|X|\). Thus this is genuinely additional data over the raw apprehension, not replacement of its anatomy by an unrelated tuple.

Both-leg enrichment is a useful sufficient construction for general re-grounding. It is not a minimality claim. On the canonical subfamily below, the occurrence is the enriched identity, and only the derivation leg needs freely chosen decoration. The general theory need not require every occurrence to have an update policy or causal-map structure.

## The composition and its exact relation to the base

Define enriched support by factorization of the entire arrows:

\[
\operatorname{Supp}_E(i,j)=\sum_{h:E(Y,X)}(h\circ p_j=d_i).
\]

Then

\[
\operatorname{comp}_E(i,j,h)=(X,h\circ d_j,p_i).
\]

The supporting equation forgets to \(U(d_i)=U(h)\circ U(p_j)\), and

\[
U_{\mathrm{App}}(\operatorname{comp}_E(i,j,h))
=\operatorname{comp}_0(U_{\mathrm{App}}i,U_{\mathrm{App}}j,U(h)).
\]

These are `support_forgets` and `reground_forgets`. Consequently, this composition is a lift of the original composition with stronger support. Raw support need not lift; the examples below show substantive extra constraints.

For \(i:A@B\), \(j:B@C\), \(k:C@D\), suppose \(h:Y\to X\) supports \((i,j)\) and \(l:Z\to Y\) supports \((j,k)\). The lift \(h\circ l\) supports \((\operatorname{comp}_E(i,j,h),k)\), since

\[
(h\circ l)\circ p_k=h\circ(l\circ p_k)=h\circ d_j.
\]

The same arrow \(h\) supports \((i,\operatorname{comp}_E(j,k,l))\), whose occurrence is still \(p_j\). Both parenthesizations yield content \(X\), occurrence \(p_i\), and derivations \((h\circ l)\circ d_k=h\circ(l\circ d_k)\). `extendSupport`, `slideSupport`, and `reground_assoc` check this witness-sensitive associativity. It compares these explicitly related witnesses, not arbitrary independently selected supports.

For any enriched arrow \(f:B\to A\), define its canonical apprehension

\[
J(f):A@B=(A,f,1_A).
\]

For \(g:B\to A\), \(f:C\to B\), the support equation between \(J(g)\) and \(J(f)\) is \(h\circ1_B=g\), so \(h=g\). Hence

\[
\boxed{\operatorname{comp}_E(J(g),J(f),g)=J(g\circ f).}
\]

This is `canonical_comp`; uniqueness of the supporting arrow is `canonical_lift`. Parameterized by their enriched derivations, these canonical apprehensions therefore have the two-sided identities and associative composition of \(E\). The orientation is deliberate: the arrow \(B\to A\) is represented by \(A@B\). General noncanonical apprehensions retain partial support and do not acquire two-sided units merely from this result. Their re-grounding-slot unit is checked separately by `reground_right_unit`.

The generic `ArrowSystem` record packages the laws needed by this transfer argument. They are not postulated for either concrete regime: the following constructions prove them.

## Lens enrichment

Take \(O\) to be small types and \(|S|=S\). Over a raw map \(g:S\to V\), add

\[
p:S\times V\to S
\]

with the two laws

\[
p(s,g(s))=s\quad\text{(GetPut)},\qquad
g(p(s,v))=v\quad\text{(PutGet)}.
\]

Thus \(E(S,V)\) is the type of total lenses \((g,p)\), and \(U(g,p)=g\). This uses the standard get/put pattern and laws from Foster et al., [*Combinators for Bi-Directional Tree Transformations*](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-popl.pdf), §§3–4 [✓]. The proofs and apprehension realization here are separate constructions, not results attributed to that paper.

For lenses \(L=(g,p):S\to V\), \(K=(h,q):V\to W\), define

\[
K\circ L=\bigl(h\circ g,\; (s,w)\mapsto p(s,q(g(s),w))\bigr).
\]

GetPut for the composite follows from

\[
p(s,q(g(s),h(g(s))))=p(s,g(s))=s.
\]

PutGet follows from

\[
h(g(p(s,q(g(s),w))))=h(q(g(s),w))=w.
\]

The identity lens has get \(1_S\) and put \((s,s')\mapsto s'\). Both unit laws follow directly. For a third lens \(H=(k,r):W\to Z\), both parenthesizations have get \(k\circ h\circ g\) and put

\[
(s,z)\mapsto p(s,q(g(s),r(h(g(s)),z))).
\]

Hence equality of all operational data proves associativity. These results construct `Lens.system`; `Lens.comp`, `ident_comp`, `comp_ident`, and `assoc` are kernel-checked.

The stronger overwrite law

\[
p(p(s,v),v')=p(s,v')\quad\text{(PutPut)}
\]

is an optional extra axiom, not needed for the category laws above. If both lenses satisfy it, then the composite does: first use PutGet for \(L\) to recover the intermediate updated view, then PutPut for \(L\) and \(K\) to collapse the successive writes. `comp_putPut` and `ident_putPut` check closure of this stronger regime. This explicitly realizes two law levels over the same get/put data.

Now represent \(L:S\to V\) by \(J(L):V@S\) and \(K:V\to W\) by \(J(K):W@V\). Their existing re-grounding composition, with support \(K\), is exactly \(J(K\circ L):W@S\). Its content remains \(W\), the content of the first argument \(J(K)\), as required by R-C2. Applying its put changes a state of \(S\); that is an action of the enriched arrow, not a violation of content invariance. Even a changed view value need not change the content object \(W\).

Enriched support is stricter than raw support. For \(S=\{0,1\}^2\), take two lenses with the same get \(g(a,b)=a\):

\[
p_0((a,b),v)=(v,b),\qquad
p_1((a,b),v)=(v,b\oplus a\oplus v).
\]

Both satisfy all three laws. Let an apprehension's derivation be \(L_0\) and the next apprehension's occurrence be \(L_1\). The raw factorization uses the identity map on the bit view. But a supporting lens \(H\) would require \(H\circ L_1=L_0\). The get equation forces \(H.\mathrm{get}=1\), since \(g\) is surjective. PutGet then forces \(H.\mathrm{put}(v,v')=v'\), so \(H\) is the identity lens. This would imply \(L_1=L_0\), contradicted by their updates of \((0,0)\) to view \(1\). Thus raw support exists while enriched support does not. This is a consequence of concrete laws, not an arbitrary support veto.

A raw map need not admit any lens structure: given a source state \(s\), PutGet supplies a preimage \(p(s,v)\) for every view \(v\). `lens_get_onto` proves this necessary surjectivity condition. No claim is made that every raw base edge lifts.

## Causal representation enrichment

Take \(O\) to be deterministic response models

\[
M=(S_M,U_M,I_M,0_M,R_M),\qquad R_M:U_M\times I_M\to S_M,
\]

with state carrier \(|M|=S_M\), external contexts \(U_M\), named allowed interventions \(I_M\), and a distinguished no-intervention element \(0_M\). Total response means every listed context/intervention pair has a unique specified outcome. This covers the response semantics of uniquely solvable structural causal models on a selected intervention family; it does not assert that all causal models have such semantics.

Over a raw state map \(\alpha:S_M\to S_N\), add

\[
\beta:U_M\to U_N,\qquad \omega:I_M\to I_N,
\]

with

\[
\omega(0_M)=0_N,
\qquad
\alpha(R_M(u,i))=R_N(\beta(u),\omega(i))\quad\text{for all }u,i.
\]

An enriched arrow is the full triple \((\alpha,\beta,\omega)\) with these laws; forgetting retains \(\alpha\). The response compatibility equation is verified in Beckers–Halpern, [*Abstracting Causal Models*](https://www.cs.cornell.edu/info/people/halpern/papers/abstraction.pdf), Definition 3.7 [✓]. The present regime additionally requires preservation of the distinguished idle intervention. It is an exact deterministic response-map regime, not a claim to reproduce every condition of their stronger abstraction definitions. In particular, no canonical derivation of \(\omega\) from \(\alpha\) is assumed.

For \(F=(\alpha,\beta,\omega):M\to N\) and \(G=(\alpha',\beta',\omega'):N\to P\), define

\[
G\circ F=(\alpha'\circ\alpha,\beta'\circ\beta,\omega'\circ\omega).
\]

The compatibility proof is

\[
\begin{aligned}
\alpha'(\alpha(R_M(u,i)))
&=\alpha'(R_N(\beta(u),\omega(i)))\\
&=R_P(\beta'(\beta(u)),\omega'(\omega(i))).
\end{aligned}
\]

Idle preservation follows by applying the two idle laws. Identity consists of the three identity functions. Associativity and both units hold componentwise, retaining the context and intervention maps rather than equating representations merely because their state maps coincide. `CausalMap.comp`, the unit and associativity theorems, and `CausalMap.system` are checked.

Surjectivity of all three maps is a further optional restriction. Surjections compose, and identities are surjective; `causal_comp_onto` and `causal_ident_onto` check closure of that regime. This still does not add the stronger semantic requirements relating intervention syntax to state abstraction. Stochastic, approximate, partially defined, and intervention-order-sensitive variants remain outside the proved construction.

The enriched closure of \(M\) is \(\sum_N E(M,N)\); an occurrence of \(X\) in \(A\) is an arrow \(E(A,X)\). Support requires an entire triple \(H\) factoring the occurrence into the preceding derivation, hence equality of all three component maps. Restriction and re-grounding are exactly the generic constructions above. For canonical apprehensions \(J(F):N@M\), \(J(G):P@N\), re-grounding with support \(G\) produces \(J(G\circ F)\). No change to the base signature or product is needed.

A nontrivial finite model is coordinate abstraction: an \(n\)-bit system has \(n\) external bits and independent interventions that either leave a coordinate alone or set it to 0 or 1. Project state, context, and intervention tuples to their first \(m\) coordinates. These maps commute with response and preserve idle. The chain \(3\to2\to1\) composes to the first-coordinate abstraction, and all three maps are surjective. This supplies populated, genuinely information-reducing models of the regime.

Not every observational correspondence lifts. On state space \(\{0,1\}^2\), contexts \(u\in\{0,1\}\), and interventions idle, `do(X=0)`, `do(X=1)`, compare

\[
M_1:X=u,\ Y=X;\qquad M_2:X=u,\ Y=u.
\]

Their idle responses coincide. Suppose the raw state identity lifted to a causal map \(M_1\to M_2\). Idle preservation and the idle compatibility equation force \(\beta(u)=u\). At \(u=1\), `do(X=0)` yields \((0,0)\) in \(M_1\), but no available intervention in \(M_2\) yields \((0,0)\) with context 1. Hence no \(\omega\) can satisfy compatibility. The finite check exhausts all 36 idle-preserving choices of \(\beta,\omega\), finding no lift. The hand argument proves the obstruction independently of enumeration.

## What changes, and what does not

The base signature changes in neither case. Its concrete closure and occurrence witnesses are enriched, and forgetting recovers their raw counterparts. Lens laws alone cannot determine a put policy from every get; causal compatibility alone cannot determine context and intervention maps from every state map. Those are genuine additions of data, followed by laws restricting that data. Further equation-only layers, such as PutPut or surjectivity, refine the enriched regimes.

This does not claim that the carrier-based raw instance is the uniquely correct base, that both legs must always share one arrow theory, or that the general theory should satisfy the category laws of its canonical subfamilies. General supported apprehensions still have the witness-dependent composition analyzed above. No `HostClosed`, fidelity order, graded support algebra, or witnessed-content transport law has been silently imported.

The earlier anatomy comparison's lens and causal examples now have explicit realizations and forgetful comparisons. In particular, the mere presence of editing or intervention operations supplies no argument for changing R-C1/R-C2. The exact construction shows how the standard serial compositions already fit re-grounding when the arguments and content indices are correctly aligned.

## Verification

[ApprehensionEnrichments.lean](ApprehensionEnrichments.lean) compiles with the installed Lean 4.33.0 toolchain using only `Std`, with no `sorry`, admitted theorem, or user-declared axiom. It checks the base conversions; support and composition forgetting; witness-sensitive associativity and the re-grounding-slot unit; canonical composition and uniqueness of its lift; both concrete arrow systems; PutPut closure; and surjectivity closure. An axiom audit found `propext` in the generic associativity proof produced by simplification; the audited canonical-composition, concrete lens/causal constructors, PutPut-closure, and causal-surjectivity proofs require no axioms beyond the Lean kernel. Proof irrelevance is part of that foundation. The type definitions, chosen semantics, and correspondence to intended applications remain outside the kernel's assurance.

[lens-causal-enrichment-checks.py](lens-causal-enrichment-checks.py) checks nontrivial finite models, canonical and noncanonical supported composition, the two lens policies and the impossibility of their enriched factorization, causal coordinate projections and recoding, and the causal no-lift example. These executable checks supplement the general proofs. Independent mathematical review and the non-strict/higher variants remain open.
