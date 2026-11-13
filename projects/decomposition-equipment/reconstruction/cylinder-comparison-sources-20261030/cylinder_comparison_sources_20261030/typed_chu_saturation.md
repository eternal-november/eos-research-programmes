# Typed two-sided context saturation: explicit Chu comparison and limits

Status: a derived theorem schema in known polycategorical/double-Chu machinery, not a claimed new Isbell distributive law or a discovery theorem from finite observations.

## A. Primary machinery located

1. Shulman, [The 2-Chu-Dialectica construction](https://arxiv.org/pdf/1806.06082), Remark 5.7, permits a Chu polycategory on a multicategory and a Set-valued presheaf even when tensor representability fails. Chu is right adjoint to forgetting a star-polycategory down to co-subunary structure. Sections 5–6 distinguish horizontal Chu arrows from vertical double-Chu arrows. This is not Garner's cylinder pseudomonad.

2. Shulman, [Star-autonomous envelopes and conservativity](https://www.cs.unibo.it/~dallago/TLLALINEARITY2020/*-Autonomous_Envelopes_and_Conservativity.pdf), Definition 4.1 and Section 7, explicitly gives multivariable forward/backward components with a common scalar composite, and double gluing. Its envelope results concern conservative formal extensions of supplied semantics, not reconstruction of physical interactions from local tables.

3. Melliès–Zeilberger, [An Isbell Duality Theorem for Type Refinement Systems](https://noamz.org/papers/isbell-final.pdf), Theorems 4.12–4.13: positive representation of a pushforward is an Isbell double-dual of the corresponding presheaf pushforward; positive representation of fiberwise tensor is double-dual of Day convolution. Raw convolution generally has only a directed comparison. These are concrete existing 'compose then close' formulas, conditional on an actual refinement system and the relevant pushforwards. The paper does not identify its double-duality closure with Garner's entire Isbell-envelope pseudomonad.

## B. Concrete nonrepresentable target

Fix a set K of observed outcomes. A pairing is A=(P_A,T_A,e_A:P_A×T_A→K).

A polyarrow f:(A_1,...,A_m)→(B_1,...,B_n) consists of functions

 f_j^+ : (product_i P_Ai) × (product_{k≠j} T_Bk) → P_Bj,
 f_i^- : (product_{h≠i} P_Ah) × (product_j T_Bj) → T_Ai,

and a common scalar function s on product_i P_Ai × product_j T_Bj, satisfying

 e_Bj(f_j^+(p,t_except_j),t_j)=s(p,t)
 =e_Ai(p_i,f_i^-(p_except_i,t))

for every applicable i,j. For arity (0,0), s is the sole datum. These are the Set-based Chu polyarrows; their composition is substitution along one matched boundary. No tensor object representing a list is required.

## C. Two-sided collapse theorem, including an honest comparison

Define p~p' iff e_A(p,t)=e_A(p',t) for all t, and t≈t' iff e_A(p,t)=e_A(p,t') for all p. Let BA=(P_A/~,T_A/≈,bar e_A). The pairing bar e is well-defined and has distinct rows and columns.

**Claim.** Every polyarrow f induces a unique polyarrow Bf between the collapsed pairings, whose component functions are obtained by taking equivalence classes of its outputs. This respects permutation, identities and polycomposition.

**Proof of the actual descent, rather than an assumption of it.** Change one positive filler p_i to an equivalent p_i'. The common scalar is unchanged, because its expression using f_i^- evaluates those two preparations against the same test. Change one negative filler t_j to an equivalent t_j'. Use its expression through f_j^+ instead. Thus s is invariant under all filler equivalences. To check f_j^+ descends, allow its missing test t_j to vary arbitrarily: the preceding invariance proves its outputs have identical rows. Dually f_i^- outputs have identical columns. This constructs the component functions on quotient sets. Substitution and quotienting commute on representatives; quotient maps are onto, so the resulting equalities hold on every quotient tuple. This proves the composition and identity laws.

**Important variance point.** There is not generally a canonical ordinary Chu arrow A→BA: its negative component would require T_BA→T_A, a choice of representatives. Instead use the double Chu category. Its vertical arrow A→BA is the pair of quotient maps

    q_A^+:P_A→P_BA,   q_A^-:T_A→T_BA,

satisfying bar e_A(q_A^+p,q_A^-t)=e_A(p,t). The component descent equations above are exactly the commuting squares giving a double-Chu cell from f to Bf with these vertical boundaries. Hence this is an explicit two-sided reconstruction/wiring comparison preserving all scalar observations, not a direct map invented by ignoring negative variance.

This theorem concerns biextensional pairing collapse, not automatically the middle object in an arbitrary CFS. Identification with such a middle requires a chosen doctrine and proof relating its factorization to this collapse. The claim is elementary and standard in spirit; no novelty assertion is made.

## D. Construct the saturated pairing from typed diagram syntax

Start with a declared collection of typed port generators and an admissible class G of finite wiring diagrams, closed under the specific gluings to be used. Work with boundary profiles when correlated multiport preparations/tests are allowed; never silently replace a joint preparation by a tuple of independent preparations.

For each boundary profile a, take P_a to be the generated preparation fragments with that open profile, and T_a the generated testing fragments with the complementary profile. These are formal sets of diagrams, or quotients by declared wiring equations. Define

    e_a(p,t)=Eval(t glued to p),

where Eval is an actual outcome assignment to the resulting closed experiments, invariant under the declared equations.

For any admitted multi-boundary wiring w, form each forward/backward residual by gluing all supplied fragments into w except the distinguished boundary. Closure of G ensures that the resulting residual belongs to the appropriate P or T. Every scalar expression in §B is evaluation of the SAME fully glued closed diagram. Therefore the Chu equations are derived from gluing associativity and Eval's equation invariance; they are not separate assumptions that wiring preserves observational equivalence. The theorem in §C then supplies the comparison for every generated wiring and its composites.

Both preparation generation and test closure are explicit here. Multiport profiles retain correlated fragments, and the polycategory avoids assuming all interactions possess tensor representatives. This construction is valid only for the admitted gluing class: unrestricted feedback/trace, cyclic gluing or analytic limits require their own defined and equation-invariant evaluation.

## E. What remains physical, not formal

The construction does **not** infer Eval on previously unmeasured closed diagrams from a local preparation/test table. Syntax tells us which experiments exist, not their outcomes. To obtain physical rather than purely formal gluing, one must supply or derive Eval from a verified interpretation of the primitive devices and interactions, or obtain the necessary contextual observations. A compositional model can establish the required equality by structural induction. An arbitrary formal completion cannot.

A tiny obstruction: two preparations x₀,x₁ have the same value against every supplied local test. Add a declared interaction g and a new final test. One interpretation returns 0 on both g(x₀),g(x₁); another returns 0 and 1. Both agree with all original local tables and use identical typed syntax. Their saturated pairings have different row quotients. Thus neither Day convolution nor Chu/Isbell free completion can choose the physically correct saturation from those tables alone.

The meaningful sufficient condition is consequently quite local: construct primitive residual transformers by actual gluing and verify their common-observation equations. Then the typed descent theorem and polycategorical substitution give all generated comparisons. This is weaker than universal representability, universal BC invertibility, or preservation of both CFS classes; stronger than merely possessing a grammar.

## F. Distributive-law audit conclusion

The bounded primary-source search located no theorem giving a physical, observation-preserving distributive law T I⇒I T for an arbitrary declared wiring monad T and Garner's Isbell pseudomonad I. This is a search result, not a nonexistence claim. Also orientation matters: a law I T⇒T I is the standard orientation used to lift T to I-algebras, whereas T I⇒I T instead naturally lifts I to T-algebras. One must specify the desired lifting, the common 2-category and the coherence axioms before writing either expression.

For the present target, a distributive law is not necessary: §C–D already constructs a genuine polycategorical/double-categorical comparison in an explicit pairing doctrine. The remaining unresolved bridge is from the user's operational primitive information to a trustworthy Eval/residual interpretation, and from this particular pairing reduction to the desired general cylinder-factorization realization. The sources above do not eliminate either bridge.

## G. Exact target, cut coherence, and additional known-status check

Let Chu_poly(Set,K) denote exactly the polycategory defined in §B, and let bChu_poly(Set,K) be its full subpolycategory on biextensional pairings. Section C constructs a polyfunctor

    B:Chu_poly(Set,K)→bChu_poly(Set,K).

For composable arrows f:Γ→Δ,A and g:A,Π→Σ with one displayed cut, its coherence statement is the equality

    B(g cut_A f) = Bg cut_BA Bf,

with the standard rearrangement of remaining boundary lists. To verify it, lift each finite tuple of quotient fillers to representatives. Both sides' forward and backward components are the quotient classes of the identical substituted original component. Independence of lifts was proved in §C; surjectivity of the quotient maps gives equality on all tuples. Associativity/interchange of independent finite cuts therefore descends, as do permutation and identity equations. This proves finite-cut coherence without invoking any tensor representative or trace.

The quotient cells are coherent horizontal cells in double Chu. No claim is made that B extends functorially to EVERY vertical double-Chu arrow; arbitrary covariant pairing maps need not preserve row equivalence against all new tests. Its asserted functoriality is on horizontal polyarrows, with its particular canonical quotient boundaries.

Additional primary source establishing the known status of collapse: Dominic Hughes, [Intensional Double Glueing, Biextensional Collapse, and the Chu Construction](https://www.entcs.org/files/mfps19/83007.pdf), §2.1.1, explicitly states functorial biextensional collapse Chu(Set,K)→chu(Set,K) and describes tensor/internal hom in the reduced category as inherited by collapse. Thus the basic reduction and compositional theme are definitely not new. The multiarrow proof above spells out the nonrepresentable/double-boundary formulation needed here; it is not presented as a novel theorem.

## H. What the Melliès–Zeilberger repair theorem actually compares

Write H_A^+ for the positive representation of the fiber over A and cl_B(φ)=⊥(φ^⊥) for its relative Isbell double dual. For a base arrow c:A→B, denote the presheaf pushforward along the induced c+ by W_c^pre. Whenever the actual pushforward c_!P exists, Theorem 4.12(b) reads

    H_B^+(c_!P) ≅ cl_B(W_c^pre(H_A^+P)).

For the fiberwise monoidal operation in Theorem 4.13 it reads

    H^+(P⊗Q) ≅ cl(H^+P ⊗_Day H^+Q).

Thus this really is a known **formal-compose-then-close versus represent-actual-composite** theorem, not merely 'if tensor preserves both classes then it commutes.' The raw Day/pushforward comparison need not be invertible; the double-dual repair is essential. But H+ is a representation of an already supplied refinement semantics, not a positive realization of experimental data. When the actual pushforward does not exist, the right-hand presheaf expression still makes sense but need not be represented by a physical object. Demonstrating such representability/positive realizability is precisely an additional burden, not a consequence of the theorem. Likewise its relative duality is not automatically Garner's entire cylinder-envelope monad.
