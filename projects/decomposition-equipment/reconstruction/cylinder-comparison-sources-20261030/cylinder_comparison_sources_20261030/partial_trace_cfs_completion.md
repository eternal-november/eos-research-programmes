# Partial-trace completion with explicit admissibility certificates

Status: bounded extension of the port-shaped reconstruction theorem to **Haghverdi–Scott partial traces**. This extends the total-trace construction. The extension retains the original domain of feedback; it does not legalize every loop available in the completion.

## 1. Primary theorem and its exact strength

Use Malherbe–Scott–Selinger, *Partially traced categories*, arXiv:1107.3608v2. Definition 3.2 specifies partial traces using directed/Kleene equalities; notably vanishing II has a defined-inner-trace precondition, while yanking is defined. Theorems 5.15–5.16 give a full faithful, trace-preserving/reflecting map into a compact closed **paracategory**. Theorems 4.29 and 4.31 complete that paracategory to a compact closed category, faithfully and trace-preservingly/reflectingly. The composite is Theorem 6.1. Corollary 6.3 permits total-trace equations when both original endpoints are defined. [Primary PDF, §§3–6](https://www.mathstat.dal.ca/~selinger/papers/ptrace.pdf).

Concretely, after harmless monoidal strictification, the target is

    D = P(Int_p(C))/~,

where P is the path category and ~ its least specified congruence. Write J:C→D for the composite. It is strong symmetric monoidal and faithful. The exact reflection equation is, for original arrows f:A⊗U→B⊗U and g:A→B,

    Tr_C^U(f) is defined and equals g
      iff Tr_D^{J(U)}(Jf) = Jg.                       (1)

**J is not asserted full.** Fullness belongs to the intermediate paracategory embedding, not generally the completed categorical embedding.

The important consequence of (1) is

    Tr_C^U(f) is defined
      iff Tr_D^{J(U)}(Jf) belongs to J(C(A,B)).         (2)

It is NOT “defined iff the completed trace exists”: the latter always exists. If J were full and (1) held, every completed trace would be Jg for an original g, forcing the original trace to be total. Thus genuinely partial traces necessarily prevent such a reflecting completion from being full.

## 2. The derived CFS completion

Assume C is small and has the specified partial trace of Definition 3.2. Then Int_p(C) is small: its objects are pairs and its arrows are specified hom-sets of C. Finite paths form sets, and quotienting by ~ preserves smallness, so D is small. Use a larger ambient universe for the generally large, locally small free Isbell envelope

    K=I(D),       H=Y_D J:C→K.

Give K the symmetric monoidal structure constructed by ext followed by I(⊗_D), as proved in `isbell_external_product.md`. Garner's Proposition 3.1 and Theorem 3.3 give its free CFS; [primary source](https://arxiv.org/pdf/1410.7108). This monoidal lifting is the separately derived construction, not an attribution to MSS.

H is faithful and strong symmetric monoidal. It is generally **not full**, unlike the fully faithful embedding available for an originally total trace. Y_D is fully faithful, but that does not repair the nonfullness of J.

Every original wire H(U) is dualizable in K, with dual Y_D((JU)*). Applying Y_D to the canonical cup/cap expression shows

    Tr_K^{H(U)}(Hf) = Y_D(Tr_D^{J(U)}(Jf)),            (3)

with strong-monoidal constraints understood. This is trace only over the designated representable wires; no compactness or total trace for arbitrary new K-objects is claimed.

Combining (1) with full faithfulness of Y_D gives the exact preserved/reflected relation

    Tr_C^U(f)=g  iff  Tr_K^{H(U)}(Hf)=Hg,              (4)

where the left side asserts definedness as well as value. Consequently

    Tr_C^U(f)↓  iff  Tr_K^{H(U)}(Hf)∈H(C(A,B)).       (5)

Proof of the reverse direction: if the K-trace equals Hg, equation (3) and faithfulness of Y_D imply the corresponding equality in D; (1) then supplies the original defined trace and its value. Thus the Isbell step does not erase reflection. Conversely, undefined original traces produce completed arrows outside the original hom-image, not admissible new values in C.

Faithfulness still guarantees Hf=Hg iff f=g for original arrows. What is lost relative to the total-trace lemma is the assertion that there are no new arrows between original endpoints. Those extra arrows are essential for representing undefined feedback.

## 3. Domain certificates for the actual network

A certificate of admissibility is part of the input semantics, not inferred from existence of a completed string diagram. One rigorous format is a finite derivation tree:

- primitive leaves have specified arrows of C;
- tensor/composition nodes use their ordinary typed operations;
- each feedback node records an already-denoted original arrow f:A⊗U→B⊗U and evidence f∈T^U_(A,B), the domain of the chosen partial trace;
- the node's original value is the specified Tr_C^U(f).

Evidence may be a domain proof or an actual witness according to the semantics; no general decision procedure is promised. A single flattened network may instead be certified as one original arrow followed by one allowed trace, if that is its declared operational interpretation. These two admission conventions must not be silently identified.

Induction on a certified derivation proves that its completed cup/cap denotation equals H of its original denotation. The trace step is (4); tensor/composition use strong monoidality and functoriality. This constructs the semantic bridge rather than assuming trace preserves E/M.

For an ordinary CFS joint preparation/test cylinder s indexed by P and Q, require a **rectangular admitted family**: every pair (a,b) in P×Q has a defined original experiment, with the specified natural context data and domain certificates for its feedback evaluations. This establishes actual entries s_ab in C for all pairs. If definedness depends jointly on (a,b) and some pairs are missing, the result is not yet an ordinary cylinder on P×Q. One must select an admitted rectangle or supply a separate partial-incidence doctrine; no undefined entry is filled by a scalar or by its completed trace. The port-shaped hypotheses are unchanged: fixed internal wire types, local primitive cylinders with their two separate natural legs, and supplied joint preparation/test maps, possibly correlated. Applying H gives the actual cylinder Hs in K.

Factor each H-image local primitive cylinder through its canonical middle M_v. The same finite port construction then gives

    W=(⊗_v M_v)⊗(⊗_internal wires H(U_e)*),
    HD --p--> W --q--> HT,
    q_b p_a = H(s_ab).                               (6)

The equality follows first in the compact target, then from the certified evaluation induction. No M_v-duals are used. The new W is an honest realization of the certified original joint cylinder, not the value of an arbitrarily totalized experiment.

Normalize p as a followed by b with a∈E and b∈M_0. Orthogonality against the canonical factorization of Hs produces

    W ←[M_0] Z →[E_0] R_K(Hs).                       (7)

Thus the positive local-to-wired comparison survives for admitted partial feedback. Neither trace nor a physical wiring functor was assumed to preserve E/M.

## 4. What reflection does not authorize

Equation (5) is a mathematical image-membership characterization, not an algorithm or an experimental admission rule. Image membership or original trace-domain membership may be undecidable. A failed or inconclusive check is not a proof of undefinedness, incompatibility, or physical inadmissibility. A certified equality of a completed **single trace of an original arrow** with Hg does prove that this trace is originally defined. Mere existence of its completed arrow does not.

Nor does a final completed denotation lying in the original image necessarily certify every intermediate node of an arbitrary nested expression. Reflection applies to a trace whose argument already denotes an original arrow. If an intermediate partial-trace node is undefined, later compact calculations do not retrospectively provide its missing original denotation or domain certificate.

Graphical rewriting in the total target can prove equalities between two certified original evaluations; it does not imply that every intermediate graphical expression is legal in the original partial semantics. In particular, rebracketing or flattening feedback must retain the stated admission convention and its domain evidence. **Operational coherence is restricted to certified admitted diagrams:** every compared operational parenthesization or intervention needs its own certificate. The partial vanishing axioms do not give unrestricted equivalence of definedness; vanishing II has its explicit inner-definedness precondition. A formal normalization inside K can still be a proof device for a globally admitted network, even when its intermediate factors are not legal physical subprocesses. Its equality is not authorization to replace execution by those intermediate operations.

Resource bounds, experimental authorization, and guards stricter than the partial-trace domain remain separate predicates on the certified network. A trace can be mathematically defined yet exceed its budget or violate a declared guard. Neither J nor Y_D automatically preserves these extra predicates or assigns a zero cost to formal cups, caps, states, or new middle objects.

If C has its own CFS, no preservation of that CFS by H is claimed. Its original middle H(R_C(s)) is another honest realization of Hs and therefore has its own controlled span to R_K(Hs), exactly as in the total-trace note. New realization objects need not descend to C or be physically implementable.

## 5. Why arbitrary guarded/partial feedback is not automatically covered

The input must satisfy the exact Haghverdi–Scott axioms, not just be called “guarded” or “partial.” A delayed trace whose type involves a delay functor rather than A⊗U→B⊗U is not directly an operation of Definition 3.2. A guard/domain restriction on correctly typed feedback can also fail its axioms.

Here is an independent finite-unrolling counterexample. On the small category of finite-dimensional rational matrices with direct-sum tensor, propose to define feedback only when its internal block T=f_22 is nilpotent, with value

    f_11 + f_12 (1+T+...+T^(n-1)) f_21,

for T^n=0. This is a plausible “finite internal unrolling” admission test, but not a Haghverdi–Scott partial trace.

Take A=B=U=V=Q and the block matrix, ordered external/U/V,

          [ 0   0   0 ]
    f  =  [ 0  -1   1 ].
          [ 0   1   0 ]

Closing V is allowed since its internal block is 0. Its resulting U-block is -1+1·1=0, so closing U afterward is also allowed, with final value 0. But simultaneous U⊕V feedback has internal block

    T=[[-1,1],[1,0]],

whose determinant is -1, so it is not nilpotent. Simultaneous feedback is undefined. The inner-trace precondition of vanishing II holds while its required equivalence of definedness fails. Thus even a concrete termination-flavored guard does not by itself qualify for the representation theorem. No claim is made that all established guarded-trace doctrines use this particular restriction.

## Conclusion

A total original trace is unnecessary: a small Haghverdi–Scott partially traced semantics suffices for the port-shaped CFS realization/span construction, **provided the actual network is certified in its original trace domain**. The completion is faithful, trace-preserving and image-reflecting, but generally not full. Undefined feedback remains outside the original hom-image; completion does not erase domain, guard, budget, or admissibility obligations.
