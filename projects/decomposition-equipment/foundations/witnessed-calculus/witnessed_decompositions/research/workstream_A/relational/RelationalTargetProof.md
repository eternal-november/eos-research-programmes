# Relational target calculus: full arbitrary-fibre proof

Author submission, 2026-10-24 UTC. Evidence class P (with the separate C oracle and optional L witness fragment). This is supporting evidence for the mandatory second A2 target, not acceptance of A1/A2 or discharge of all C2. Contract v0.1-proposed, SHA256 `47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`; A1/A2 freezes and the 18:10 UTC A2 pre-attempt PASS apply without weakening.

## 1. Quantifiers, operations, and exact types

Fix an arbitrary interface type I, arbitrary quiver J on I, and arbitrary component-indexed types X(c), where c is a full component `(A,B,j : J(A,B))`. No carrier is assumed inhabited, finite, decidable, discrete beyond its ordinary equality, or independent of c. In the tests each X(c) is Bool, but the theorem does not make that restriction. Universes are arbitrary, subject only to the usual maximum needed for dependent products, predicates, and sums.

For an endpoint-typed path p : Path(c.source,c.target), put

    V_X(p) = Π i : Path.Slot(p), X(Path.componentAt(p,i)),
    Rel_X(c,p) = V_X(p) → X(c) → Prop.

These are all relations, not functional relations and not a single Boolean indicating whether a relation is nonempty. Equivalently they are subsets of `V_X(p) × X(c)`. Relation equality is extensional equality of those subsets/predicates. The output c and the complete ordered path p are part of the fibre. Carriers happen to coincide in a test does not authorize coercion between different fibres.

For equality e : c=d write `e_* : X(c) → X(d)` for equality transport. For equality h : p=p' of paths with the same fixed endpoints, write

    h_* : V_X(p) → V_X(p')

for `Path.pathFamilyCast X h`. It is a bijection with inverse `(h.symm)_*`. Relation transport is

    h_*^Rel(R)(v',z) := R((h.symm)_* v',z).

These transports are equality elimination, not choices. Naturality, inverse, and composite laws follow by eliminating the equalities. In Lean, equality of predicates additionally uses propext and funext; neither supplies data or classical choice.

Let p be any path and q_i : Path(c_i.source,c_i.target), where c_i = componentAt(p,i). The ordered, component-preserving bijection is

    E = Path.slotExpand p q : Slot(expand p q) ≃ Σ i : Slot(p), Slot(q_i).

For k=E^{-1}(i,j), the named equality

    e_ij : componentAt(expand p q,k) = componentAt(q_i,j)

is `Path.componentAt_slotExpand_symm p q ⟨i,j⟩`. For v : V_X(expand p q), define the restricted input tuple

    v_i(j) = (e_ij)_* v(E^{-1}(i,j)).

This is exactly `Path.expandFamily X p q v i`, and has type `V_X(q_i)`. Conversely, given b_i : V_X(q_i), define the assembled tuple b at k by writing E(k)=(i,j) and transporting b_i(j) backwards along the corresponding component equality. These two constructions are inverse: applying E then E^{-1} cancels, and the forward/backward equality transports cancel. The construction keeps the indices (i,j), including repeated equal c_i, not just their component labels.

For R : Rel_X(c,p) and S_i : Rel_X(c_i,q_i), define simultaneous substitution by

    (R[S])(v,z) iff ∃ a : V_X(p), R(a,z) ∧ ∀ i : Slot(p), S_i(v_i,a(i)).        (1)

It is an operation of Rel_X(c,expand p q). The unique intermediate value at occurrence i is a(i) : X(c_i), used as that inserted relation's output and that occurrence's outer input. Different occurrences with the same c_i have independent values. No exchange, contraction, or copying is inserted. Existential quantification may forget witnesses semantically; it does not assert that different source presentations are equal.

For the singleton path `[c] = c.edge.toPath`, with its unique slot `star = Sum.inr ()`, define

    id_c(v,z) iff v(star)=z.                                                 (2)

Every other slot is impossible. Empty paths occur only at equal endpoints. An operation at the empty path is an arbitrary predicate on X(c), with c a loop: its input tuple type has one empty function. It need not be true, nonempty, or an identity.

## 2. Constructive finite witness assembly

The only potentially choice-looking step in associativity is the implication

    (∀ i : Slot(p), ∃ b_i : Y_i, P_i(b_i))
      ⇒ ∃ b : Π i : Slot(p), Y_i, ∀ i, P_i(b(i)).                            (3)

Here Y_i may itself be an arbitrary dependent function type and may be empty. Proof is finite dependent induction on p. For nil, Slot(p) is Empty; use the empty function and eliminate the impossible i. For cons p e, Slot is Slot(p) ⊕ Unit. Apply the induction hypothesis to the inl-indexed family, eliminate its existential into the final existential proposition to obtain b_old, and eliminate the supplied existential at inr() to obtain b_new. Define b(inl i)=b_old(i), b(inr())=b_new; the corresponding proofs are the two supplied proofs. No existential in Prop is eliminated to produce globally selected data in Type: the conclusion itself remains an existential proposition. The reverse direction takes evaluation of an already supplied b. This is finite constructive choice, derivable in intuitionistic dependent logic, with no axiom of choice or excluded middle. It works even when p has no slots. `RelationalWitnessLemmas.lean` checks this lemma against the actual Path.Slot datatype.

## 3. Both units, with named profile transport

### Right unit

Take S_i=id_(c_i), q_i=[c_i]. Let h=Path.expand_edges p, so expand p q=p. For v : V_X(expand p q), equation (1) becomes

    ∃ a : V_X(p), R(a,z) ∧ ∀i, v_i(star)=a(i).

The tuple on the left in the final equality is `(h_* v)(i)`, by `Path.expandFamily_edges X p v i`. Thus a exists exactly when R(h_* v,z): in the forward direction, dependent function extensionality gives a=h_*v and we substitute that equality; in the reverse direction choose the explicit tuple a=h_*v. The pointwise equivalence says precisely

    h_*^Rel(R[id]) = R.

For p=nil both tuples are the unique empty function, and the same argument uses the empty universal conjunction. It does not assume that X(c) is inhabited or that R contains a pair.

### Left unit

Take arbitrary S : Rel_X(c,q), including q empty when c is a loop. Substitute S into the sole slot of id_c. Let h=Path.expand_edge c (singleton profile family), so the expanded path is q. Equation (1) is

    ∃ a : V_X([c]), a(star)=z ∧ S(v_star,a(star)).

By `Path.expandFamily_edge`, v_star=h_*v as dependent tuples. Forward: replace a(star) by z. Reverse: define the singleton tuple a(star)=z and eliminate its impossible other slots. Therefore the displayed proposition is equivalent to S(h_*v,z), proving

    h_*^Rel(id_c[S]) = S.

This does not require selecting z: z is the already fixed output in the pointwise statement. Thus empty X(c) causes no exception.

## 4. Associativity, with all output/component transports

Fix R : Rel_X(c,p), S_i : Rel_X(c_i,q_i), and for each

    k : Slot(Q), Q=expand p q,

a profile r_k with output component d_k=componentAt(Q,k) and relation T_k : Rel_X(d_k,r_k). Put

    L = expand Q r.

For each i,j set k_ij=E^{-1}(i,j) and e_ij : d_(k_ij)=componentAt(q_i,j) as in §1. Transport the entire operation (r_(k_ij),T_(k_ij)) along e_ij. Its transported profile is

    r'_ij = Path.expandFamily (fun d => Path(d.source,d.target)) p q r i j,

and its transported relation is T'_ij : Rel_X(componentAt(q_i,j),r'_ij). This means equality transport of BOTH the input path and the output carrier, not an untyped reuse of a table. Concretely, eliminating e_ij makes T'_ij=T_(k_ij); this characterizes the transport without an arbitrary cast convention.

Define Q'_i=expand q_i r'_i and P'=expand p Q'. The canonical equality is

    h = Path.expand_assoc p q r : L=P'.

The exact fibre law is

    h_*^Rel((R[S])[T]) = R[ (S_i[T'_i])_i ].                                (4)

Fix v : V_X(L) and z : X(c). For each k let v_k be v restricted through slotExpand Q r. For each i,j let v_ij be its corresponding transported restriction, of type V_X(r'_ij). The coherence theorem `Path.expandFamily_assoc X p q r v i j` states exactly that restricting h_*v on the right side first to Q'_i and then to r'_ij gives v_ij. This theorem is derived from `Path.slotExpand_assoc`: a final slot reaches the SAME ordered triple (i,j,l) on both sides, and the component transports coincide. It covers empty blocks. It is not merely an equality of frontier lengths or profiles.

Unfold the left side of (4) before transporting its input. Its membership at (v,z) is

    ∃ b : V_X(Q),
      (∃ a : V_X(p), R(a,z) ∧ ∀i, S_i(b_i,a(i)))
      ∧ ∀k : Slot(Q), T_k(v_k,b(k)).                                      (5)

Use the explicit tuple bijection in §1 to write b as the independent family

    b_i : V_X(q_i).

Reindex the last universal condition along E. Equality transport of T_k makes it exactly `∀i ∀j, T'_ij(v_ij,b_i(j))`. This change is reversible: E is a bijection, its component transports have explicit inverses, and equality elimination verifies transport compatibility with predicate application. Consequently (5) is equivalent to

    ∃ a : V_X(p), ∃ b : Πi, V_X(q_i),
      R(a,z) ∧ ∀i, (S_i(b_i,a(i)) ∧ ∀j, T'_ij(v_ij,b_i(j))).                (6)

Here swapping the two outer existentials and rearranging conjunctions are constructive logical equivalences. Formula (6) implies

    ∃ a : V_X(p), R(a,z) ∧
      ∀i, ∃ b_i : V_X(q_i), S_i(b_i,a(i)) ∧ ∀j, T'_ij(v_ij,b_i(j)),         (7)

by projecting the supplied family. Conversely, given (7), fix its supplied a and apply finite witness assembly (3) to the predicate in its last line to obtain the b family in (6). This is the only assembly step, and it uses no classical choice. Finally, (7) is exactly membership in R[(S_i[T'_i])_i] at (h_*v,z), by (1) and the named restriction coherence above. We have proved both directions of (4) for every input and output; relation extensionality finishes the equality.

No restrictions on any relation, profile length, or value type entered the proof. If p is empty, there is one empty a and no S_i. If a q_i is empty, b_i is the empty function and no T'_ij is requested, but S_i may still restrict its output a(i). If any r_k is empty, v_k is the empty input and T_k remains an arbitrary predicate on its intermediate output. These are precisely the nullary behaviors, not special conventions imposed after the proof. If c_i=c_j for i≠j, b_i and b_j remain independently indexed; nothing in the proof identifies them.

## 5. Exact comparison with the integrated total-space Calc

The integrated `WitnessedDecompositions/Calculus.lean` encodes a calculus by total operations with a profile map, not directly by arbitrary fibres. Take

    Op(c) = Σ p : Path(c.source,c.target), Rel_X(c,p),
    profile(p,R) = p,
    identity(c) = ([c],id_c),
    subst((p,R),f) = (expand p (i ↦ profile(f_i)), R[(f_i).relation]).

This is `Collection.totalize Rel_X` at the collection level. In the last formula f_i has exactly output component componentAt(p,i), so all types are as in §1. `profile_identity` and `profile_subst` are definitional equations. The profile in `CalcData.identityFamily`, `CalcData.innerFamily`, and `CalcData.composeFamily` is precisely this p, not a presentation's leaves.

To prove each total-space Calc law, use its named profile equality from §3 or §4 for the first component of the dependent pair and the corresponding relation equality after transport for the second. Equality of dependent pairs then proves the law. In particular, `CalcData.innerFamily` first pulls the third-stage family along `profile_subst`, then applies `Path.expandFamily` to the total operations. This is exactly the transported pair (r'_ij,T'_ij) in §4. Therefore `Calc.subst_assoc` is (4), not a weaker pointwise or fixed-profile statement. No desired law is inserted as a new field assumption: §§3–4 prove the required fields from the independent relation construction.

The prescribed operation fibre of this totalization is

    { (q,R) : Op(c) // q=p }.

Its explicit equivalence with Rel_X(c,p) sends ((q,R),h) to h-transport of R and sends R to ((p,R),rfl). Both composites reduce to identity by eliminating h. These are exactly `Collection.fiberTotalizeEquiv` and its inverse. They preserve identities by (2), and substitutions by (1) after eliminating the input profile equalities. This is also the special case of `Collection.fiberFamilyEquiv`: independently prescribed replacement profiles/fibres and total replacement operations are equivalent, including empty families.

Conversely, for any integrated Calc M, take its genuine fibres `M.Operation c p`, its `identityOperation`, and `substitute`. The direct arbitrary-fibre laws are the already named `Calc.substitute_identity`, `Calc.identityOperation_substitute`, and `Calc.substitute_assoc` with exactly the transports used above. Totalizing these fibres gives an operation-space equivalence

    (p,(a,proof(profile(a)=p))) ↦ a,
    a ↦ (profile(a),(a,rfl)),

namely `Collection.totalizeFiberEquiv`. It preserves identities and all substitutions by the definitions and equality elimination. Thus taking genuine fibres and totalizing are two-sided equivalences of these formulations, not a one-way model embedding.

For maps, a family of fibre maps preserving identities and substitution totalizes as `(p,R) ↦ (p,F_p(R))`; a strict integrated `Calc.Hom` restricts to `onOperation`. Profile equalities make the reverse construction inverse, and the `map_identity` and `map_subst` laws become exactly the corresponding fibre laws after eliminating those equalities. Identity maps and compositions are preserved pointwise. Therefore the comparison applies to targets and strict morphisms, as required to instantiate the arbitrary-target universal property.

This file is a P construction of that full relational Calc. The separate Lean witness file checks finite assembly and the logical associativity step, not the full totalized Calc instance. That limitation is explicit and does not relabel P evidence as L. The A2 generic extension, substitution preservation, uniqueness among all strict morphisms, inverse laws, and categorical packaging are separate obligations handled by the integration owner.

## 6. Interpretation and finite nonvacuity certificate

For any typed signature S, an assignment a_g : Rel_X(result(g),input(g)) interprets an identity edge by (2) and a node by (1). Once the generic A2 extension theorem is applied to the Calc just constructed, this recursion is its unique strict extension. Directly, the same formula says that a pair belongs to a tree's relation exactly when there exist values on its internal edges making every assigned vertex relation true, with the supplied external-input/output values. This characterization follows by tree induction using finite assembly at each node. The oracle independently checks both recursive substitution and global internal-edge existential evaluation; it does not assume the A2 theorem to compare tables.

The exact finite signature, all multivalued tables, full-boundary rejection certificates, four-leaf mixed tests, independent repeated-slot substitutions, nullaries, and exhaustive-domain counts are specified by `FiniteModel.md`, `check_relational_model.py`, and its saved JSON report. In particular, the nested test uses the full mixed path x:A→B, r:B→B, r:B→B, y:B→C with a genuinely value-bearing repeated r, and two legal images for the same parallel primitive. Distinct corolla images already force distinct strict extensions; the nested witness additionally verifies that the distinction survives a nontrivial context. Nothing here asserts injectivity of relational semantics, freeness of the relational target, or any graph-cut/equipment/2-Segal result.

## 7. Proof dependencies and status

Required mathematical inputs: ordinary dependent equality elimination and function/predicate extensionality; the ordered Slot/expand correspondence with inverse/component/coherence laws; finite dependent induction on paths. No excluded middle, infinite choice, nonemptiness, decidable equality, reconstruction property, or restriction to finite carriers is assumed. The optional Lean fragment's exact kernel axiom report is recorded separately; it is not a claim that the full P proof was Lean checked.

Integrated declarations referenced: `Path.slotExpand`, `Path.componentAt_slotExpand_symm`, `Path.expandFamily`, `Path.expand_assoc`, `Path.slotExpand_assoc`, `Path.expandFamily_assoc`, `Path.expandFamily_edges`, `Path.expandFamily_edge`, `Collection.totalize`, `Collection.fiberTotalizeEquiv`, `Collection.totalizeFiberEquiv`, `Collection.fiberFamilyEquiv`, `Calc.substitute_identity`, `Calc.identityOperation_substitute`, `Calc.substitute_assoc`, and `Calc.Hom.onOperation_substitute`. Their source hashes at evidence generation are recorded in `EvidenceManifest.json`. Any later source change requires rechecking this comparison; a name alone is not evidence of the theorem statement.
