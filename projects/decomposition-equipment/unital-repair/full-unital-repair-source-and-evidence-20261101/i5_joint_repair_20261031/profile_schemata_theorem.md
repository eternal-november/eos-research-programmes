# Full-profile active-label repair theorem and finite certificate

31 October 2026. **Theorem for the declared independent active-label extension, subject to its explicit old-operation hypotheses; not a theorem for unrestricted original C5 scalars.** Analytic scalar proof: `monoid_repair_theorem.md`, §§1–5. The coordinate argument and final quantitative synthesis (§§8–9) received independent framing-auditor review. This file supersedes `profile_schemata_draft.md`: the selected discrete endpoint and its uniform elementary-round upper bound are proved under §1 hypotheses; no general finite old-profile normalization theorem is claimed. This note separates three claims which must not be conflated: finite label templates; a sound uniform partition; and the coarsest partition on all full old-profile sorts.

## 1. Setting and indispensable hypotheses

Fix graph vertex bound N, finite monoid P, and the declared graph-cut doctrine. Every concrete old operation/profile/witness record remains EXACT observable data. Over any fixed such record s with r nonempty ordered inputs, the new-label fibre is X_s=P^r, where 0<=r<=N. There is one point for r=0. Arbitrarily many empty inputs remain tagged positions in s; they carry no label. If a profile admits several old witnesses, apply this statement separately over each old witness, not to their union.

Assume the decoration is a genuine independent extension: every tuple in P^r is allowed; old definedness is independent of labels; a permitted old graft/cut/transport has exactly the new-label equations declared below, without additional label-dependent guards. All exact old data and cut skeletons are retained in observations. These assumptions require checking against the selected C5 extension, not against an abstract label operad alone.

For the necessity theorem in §4 require the following ACTUAL operations over every old record: (a) substitution of a labelled unary identity at any nonempty input; (b) postcomposition by a labelled unary identity of the output; (c) the cut expressing the original operation as outer operation of the same old profile followed by one unary identity at each input (empty children have no new label); and (d) the declared channel swap, if used, including its inverse. Identity arrows suffice, so no arbitrary interface arrow is needed here.

## 2. Complete finite label templates with old guards

Delete empty positions only from the indexing of NEW labels, never from the sort or old cut witness. For a one-level ordered cut with r external active inputs and m active parent inputs, each active parent has at least one active child. Thus 1<=m<=r<=N and the active children form an ordered composition r=r_1+...+r_m with r_i>=1. Its label relation is

    R_g(x;a,b) iff x_j=a_{g(j)} b_j for j=1,...,r,

where g:[r]→[m] is the corresponding monotone surjection. The parent is labelled a∈P^m, and b∈P^r is packaged into child tuples of lengths r_i. The parent factor a_i is SHARED by every child in its group. The cut observation must use the whole tuple (a,b), not separate coordinate marginals.

There are exactly 2^(r-1) such grouping templates for r>0. If vertex sizes matter, decorate active nodes with positive sizes, summing to at most N, and require parent size to equal the sum of child sizes. There are finitely many such decorations. Graph edges, interface arrows, occurrence maps, arbitrary empty positions and frame types remain in the EXACT OLD GUARD: this template applies only to an actually permitted old cut witness. A guard is not dropped merely because its label equation exists.

Every actual one-level cut projects onto its grouping template. More strongly, over EACH fixed admissible old skeleton the projection onto label solutions is surjective: every solution (a,b) may decorate that skeleton. This is a direct consequence of the independent-extension hypothesis. Conversely any decorating cut projects to a solution. This is the needed fibrewise surjectivity/reflection statement; it does not assert that every template is admissible at every profile.

Grafts use the same grouping map and equation, read as the deterministic map (a,b)↦x. Fixing all but one actual argument gives elementary one-hole contexts. Unary chains introduce successive multiplication, not additional independent external labels. Associativity proves the tree graft law: each leaf receives the ordered product along its path. No commutativity is used.

An arbitrary generated finite graft/cut tree is covered by iterating these bounded-arity templates at its nodes. Empty-only nodes contribute unique new-label tuples; arbitrary chains through empty old interface arrows remain exact old skeletons. Their length is NOT bounded. Any effect on feasibility is still checked in the old skeleton.

For a finite declared frame action, transport acts by the specified label automorphisms/channel permutations and any induced active-position permutation. More generally it is enough that the declared action has a proved finite effective image on all P^r, r<=N. A finite set of interface OBJECTS alone does not establish this hypothesis.

Stability for elementary grafts implies stability for arbitrary generated graft contexts by composition and changing one variable occurrence at a time. Stability for elementary JOINT cuts implies preservation of all finite cut-tree tests: match the root joint record, then match each selected child subtree while retaining its already selected root witness. This induction is valid for the declared factorization trees; crossing cuts or extra shared variables between separate child subtrees require an additional compatibility theorem. Exact old skeleton observations ensure matched nodes have identical old feasibility data. A finite set of label templates does not erase those data.

## 3. What this does NOT yet prove

A uniform family of partitions E_r on P^r stable under EVERY label template lifts to a stable partition on every actual profile. This is soundness. It need not be coarsest: a particular old sort may admit fewer tests than the template union. Finite N and finite P alone do not justify identifying all sorts of active rank r or solving one global template table and declaring its answer minimal.

To prove a general coarsest schema theorem one would need finite effective old behavioral types plus a lifting/back-realization theorem for every splitter, or canonical-profile realization and sufficiently strong actual comparisons to carry necessity to every sort. The finite category of interface arrows, graph data, and empty-chain normalization would have to be specified and proved. Retaining an unevaluated old-profile guard is not by itself a finite algorithm for all infinitely many profiles.

For the PRESENT candidate, there is a stronger route that avoids this unsupported general theorem.

## 4. Coordinate necessity lemma and exact discreteness theorem

Let q be the initial scalar observation on P, applied coordinatewise at every active input. Define a finite monoid partition iteration D_t starting with D_0=ker(q). Each step retains D_t and all of:

* D_t(az) and D_t(za), for every a∈P;
* F_t(z)={(D_t(u),D_t(v)):uv=z};
* D_t(τz), for every declared label-transport generator τ.

Let E be ANY global S/C/T-stable typed partition refining the starting observations, with no uniformity or product-form assumption. Then for every old record s, every coordinate i, and every t,

    x E_s y  =>  x_i D_t y_i.

Proof by induction. The base is coordinatewise initial observation. For right multiplication, graft the unary labelled identity a at input i; for left multiplication, postcompose with the unary labelled identity a. The latter multiplies ALL active coordinates, but projecting the induction conclusion to coordinate i is enough. Transport uses its actual typed action and the corresponding coordinate/frame identification.

For the factorization step use the actual cut in §1(c). A concrete joint factorization consists of outer labels u_1,...,u_r and unary child labels v_1,...,v_r with u_jv_j=x_j. By induction, each E-class of the outer tuple determines D_t(u_i), and the E-class of unary child i determines D_t(v_i). Projecting the FULL joint E-cut signature to these two determined values gives EXACTLY F_t(x_i): any factorization of x_i extends to the other coordinates using u_j=x_j,v_j=e. Hence equality of the full joint signatures implies equality of F_t(x_i), independently of any correlations or extra distinctions already present in E. This proves the induction. Empty coordinates contribute nothing.

Consequently, if the finite monoid S/C/T optimum D_* is discrete, EVERY permissible stable E is discrete on every old-record fibre. The identity partition is itself stable under all actual maps and relations, including all guarded old cuts and all generated contexts. Therefore it is the COARSEST simultaneous refinement on the entire infinite family of full old-profile sorts.

This proves both necessity and sufficiency without quotienting profiles, without assuming finite contexts, without requiring all intermediate repairs to have a uniform product form, and without any finite old-skeleton normalization theorem. The proof uses only the actual local identity schemata for necessity; arbitrary old guarded operations are harmless for sufficiency because the final partition is discrete.

For P=M_k×M_k with q((f,g))=H-membership(f), channel swap exposes H-membership in both channels. The analytic proof in `monoid_repair_theorem.md` §4 establishes that S/C completion of H-membership on M_k is discrete: index tests separate indices; left multiplication by a isolates A_1; the cut predicate “has left factor A_1” separates the constants; right multiplication by b and ab separates all remaining pairs. Consequently the global least simultaneous refinement is discrete, with exactly

    |P|^r=(3k−2)^(2r)

classes over EVERY exact old record of active rank r. No product-form assertion about intermediate graph repairs is used.

## 5. Effective representation and honest costs

For the discrete conclusion, the output schema is simply: retain exact old data and the complete ordered active-label tuple. No enumeration of old profiles is needed. Given a concrete record, locating active occurrences and outputting their labels is effective provided the old record format/operations are effective. Hidden information costs r·ceil(log2 |P|) bits in a fixed-width encoding, up to framing overhead; at r=N there are |P|^N distinct classes. This is a genuinely exponential state count in N, not a compact partition-table claim.

The finite necessity certificate is checked on the monoid P alone. With p=|P| and an explicit multiplication table, each combined refinement round can compute factor signatures by enumerating p² products and left/right signatures by O(p²) table lookups, plus transport lookups. Using p²-bit factor-signature vectors and radix sorting gives a conservative O(p³) table/word accesses per round and O(p⁴) total over at most p−b_0 strict block-increasing rounds (plus the final test), with O(log p)-bit indices and O(p³) bits of signature working memory. Charging O(log p) per indexed-word access yields the conservative O(p⁴ log p) indexed-word bit charge; this is not a hardware-independent O(p⁴) pure-bit runtime claim. Better sparse/hashed implementations are possible but not needed for the bound. These are combined elementary rounds, NOT full S/C/T sweep counts.

For finite active-label template verification there are B=sum_{r=0}^N p^r carrier points across formal rank sorts. At rank r there are 2^(r−1) cut groupings; each has at most p^(m+r)<=p^(2N) label records. Therefore total undecorated cut-record count is at most 2^N p^(2N) including the unique rank-zero template, before finite size/frame decorations. Graft table entries have the same bound. These are finite LABEL-table costs, not an enumeration of actual old cuts. Arbitrary generated depth is justified by the induction in §2, not by pretending those contexts form a finite set.

## 6. Audit checklist

1. Check every old record admits the exact identity grafts and all-input unary cut used in §4, with labelled decorations fully independent.
2. Check old data are observed exactly, including any old witnesses rather than just nominal profiles.
3. Import the analytic M_k discreteness proof in `monoid_repair_theorem.md` §4, not merely numerical sweeps or first noncommutation.
4. Check the channel swap has the stated actual interface/frame realization.
5. Do not promote §2's guarded coverage into a general finite coarsest-profile theorem.
6. Do not extend cut-tree induction to non-laminar/crossing or externally correlated cuts without a separate witness theorem.


## 7. Positive non-discrete shared-parent control

Let the added label monoid instead be a finite group G, let H◁G be a proper nontrivial normal subgroup, and observe each active label in G/H. Suppose declared label transport preserves H. This coordinatewise quotient is already S/C/T-stable on EVERY old-profile fibre; its least simultaneous refinement is therefore itself.

The nontrivial point is a joint cut with a shared parent a_i. Given a concrete factorization x_j=a_i b_j and another x' with x'_jH=x_jH, retain ONE same parent representative a'_i=a_i for the whole group, and define b'_j=a_i^{-1}x'_j. Then a'_i b'_j=x'_j and b'_jH=b_jH for all j simultaneously. Parent and all child tuple quotient values are unchanged. Reversing x,x' proves equality of complete joint cut signatures. Normality gives substitution congruence; H-invariance gives transport congruence. Exact old skeletons and feasibility stay unchanged. This is genuine shared-parent lifting, not a marginal-factor argument.

A nontrivial one-pass transport example takes G×G with initial observation only the first channel modulo H and declared channel swap. Initial S and C repairs do nothing; T yields the product of both coset observations, which remains S/C-stable by the same proof. Thus one T pass gives the least simultaneous refinement, with [G:H]^(2r) rather than |G|^(2r) classes in rank r. This contrasts genuinely with the M_k discrete endpoint, while avoiding a claim that generic equivariance makes C commute with T.


## 8. Uniform all-profile stabilization bound

Define G_0 to be the starting typed partition family. Define G_(n+1) by retaining G_n and adjoining, simultaneously, signatures for every declared elementary one-hole graft, every elementary joint cut, and every declared elementary transport. This is a mathematical family of splitters on ALL exact old sorts, not a finite enumeration of those sorts. For the upper bound, elementary grafts include unary identities with EVERY label in P; this is a finite multiplier palette. In particular right multiplication by ab is ONE such elementary labelled context. If instead the primitive basis contains a,b in BOTH channels, namely (a,e),(b,e),(e,a),(e,b), add one round for the right-ab word. First-channel generators plus swap alone require separately counting conjugation and do not justify the same optional bound.

**Stagewise coordinate lemma.** Suppose a family of scalar predicates is determined by G_n on each corresponding active coordinate at every profile. Then its scalar left/right-multiplication refinements, joint-factor refinements, and transport refinements are determined by G_(n+1). The proof is the induction in §4 with E replaced by G_n at outputs and G_(n+1) at sources. In particular, the cut projection is well-defined because every G_n output class determines the required stage-n scalar class; equality of complete joint G_n signatures implies equality of the projected scalar factor signature. It does not require G_n itself to be stable or uniform.

Put

    R(k)=max(2, ceil(log2(k−2))).

The exact scalar cut calculation in `monoid_repair_theorem.md` §5 shows that R(k) elementary C steps distinguish all scalar indices. A valid stagewise test schedule is:

1. One T step exposes H-membership in both channels.
2. R(k) C steps determine index in both channels at every active coordinate.
3. One S step (left a in either channel) isolates each A_i with i<=k−3, in particular A_1.
4. One C step using the class of A_1 distinguishes A_(k−1) and B_(k−1).
5. One S step using right b and right ab distinguishes every remaining pair.

These scalar channel-specific multipliers are labels (a,e), (e,a), (b,e), (e,b), (ab,e), (e,ab) in P. Extra global splitters can only make G_n finer, so the combined splitter process satisfies

    G_(R(k)+4) = identity on EVERY old-profile fibre.

It is therefore stable by that stage, uniformly in old arity, empty insertions, graph/profile names, and generated unary depth. If the elementary multiplier basis contains the four separate a,b generators in BOTH channels specified above, the same reasoning gives the conservative bound R(k)+5. These are upper bounds on combined elementary rounds, NOT asserted exact bounds, NOT counts of full saturated S/C/T sweeps, and NOT a claim that infinitely many old guards can be enumerated by a finite global partition table.

The endpoint has a finite effective certificate: check the finite monoid table and explicit scalar tests, prove the identity graft/cut realization once as an old-operation schema, then apply the stagewise lemma. Computing the output on any given concrete record just retains its labels. General intermediate global repair families need not have product form. In particular, the independently reported rank-two M_4 calculation finds 38 scalar C-blocks rather than the 16 predicted by Q×Q; this computation is a warning, not a premise of the theorem.

## 9. Information, algorithms, and a concrete compressed control

Let m=3k−2 and p=m². Over active rank r the initial first-channel H tuple has 2^r classes, while the least simultaneous repair has p^r=m^(2r) classes. Any injective fixed-length hidden-label code therefore requires at least ceil(2r log2 m) bits; independent fixed-width coordinate coding uses at most 2r ceil(log2 m) bits. The theorem is an exact class-count/necessary-information result. It is not a physical sensor-acquisition theorem: the required full label witnesses must already be available symbolically or supplied by an additional information-access mechanism.

An explicit quotient table has exponential size in N. A tuple representation and its finite proof schema do not remove that state-count lower bound; they avoid enumerating the states. Runtime for processing a concrete record includes reading/checking its exact old data, whose size is not bounded by N alone because empty positions and paths remain unbounded. The finite P-certificate costs in §5 are distinct from that record-processing cost and from the elementary iteration bound in §8.

For the positive group control take G=C4 (additive integers modulo 4) and H={0,2}; then G/H=C2 is proper and nontrivial. With two channels G×G and initial first-channel parity, T adds second-channel parity in one pass. All ordered shared-parent cuts preserve the resulting parity tuples by §7. At active rank r the stable quotient has 4^r classes whereas the actual label fibre has 16^r points. Thus the positive control is genuinely non-discrete and includes nontrivial transport and correlated multi-input cut lifting.
