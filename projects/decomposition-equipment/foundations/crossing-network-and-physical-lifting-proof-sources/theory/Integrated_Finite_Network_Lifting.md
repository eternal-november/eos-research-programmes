# Finite hardware-bounded reconstruction of a shared component across crossing charts

## Plain-language abstract

The question is whether several locally correct decompositions can describe one component that the permitted hardware can actually build. A correct answer must retain the same actual system events across overlapping views, preserve distinctions that a local decomposition needs, and use one implementation rather than quietly choosing different devices in different contexts.

This theorem combines those requirements into one terminating construction. It starts with the actual parent systems and their crossing matchings, not with a compatible component already supplied. It generates the possible local reconstructions, derives the forced identifications from shared events, checks exact interface coverage and any required operations, and compiles one allowed device together with its actual interface adapters. The hardware bounds even the event sectors that were mathematically unbounded when nothing could observe them. A successful result includes the component, its factorization maps, and circuit witnesses; failure is relative to the declared finite hardware grammar, not every conceivable machine. Full execution of the surrounding system additionally requires implementations of the surrounding components.

The finite partition and circuit-synthesis mechanisms are standard. The point of this integrated result is that their comparison is exact: the same quotient events must be the same physical records in every chart, and no interface operation is declared physically available merely because it exists in finite-span semantics.

## 1. Precisely declared problem

### 1.1 Structural input

Fix one designated component occurrence v in a finite family of crossing charts. In chart i the input is the finite four-component schema of the cylinder theorem in `../foundations/Crossing_Grid_Cylinder_Reconstruction.md`: fixed R_i,Q_i,S_i, parents P_i,N_i, and actual whole-witness bijection θ_i. The unknown local component is T_i. Its factorization maps must satisfy the original equation

    θ_i((α_i(r,t),q),s)=((r,q),β_i((t,l),s)).          (1)

Every witness, its endpoints, and θ_i are explicit finite tables. Empty fibres are allowed. No choice of α_i,β_i or T_i is assumed in advance.

The globally shared component has source B and target C, with boundary-profile carrier E=B×C. For chart i its boundary-profile carrier is E_i and its prescribed profile map is p_i:E_i→E. In the ordinary span-restriction case E_i=B_i×C_i and p_i=f_i×g_i. The carrier reconstruction also works for arbitrary profile maps p_i; such a map is not automatically an equipment restriction or physically executable adapter. The operational certificate below decides the admitted subclass.

The same fixed actual whole W is carried as data, with chart exposure domains D_i and actual identifications of exposed events with chart whole tuples. They can be genuine endpoint restrictions, as in the active cycle example; if instead they are witness selections, that distinction is explicit. From each selected α_i,β_i, equation (1) extracts π_i:D_i→T_i. Whole-event equality supplies forced identifications π_i(w)~π_j(w). The input may additionally require assembly of global parents: then every actual shared parent event supplies its corresponding inverse-factorization anchor as well, even if it has NO whole extension because Q or S is empty. Unchanged context coordinates must also agree. These are derived from the primitive factorization tables, not supplied overlap isomorphisms.

Optional operational data are a finite many-sorted partial-operation signature and explicit local/base operations as in Theorem 2 of `Anchored_Network_Reconstruction.md`. They must be interpreted as actual model operations. Ordinary span witness carriers are not assumed to have a successor operation by default. If their carriers are not yet selected, local operation tables are additional finite unknowns, enumerated with each bounded carrier and checked against explicitly supplied finite model equations. Any required physical interpretation of those operations must likewise be computed from the compiled record semantics or supplied as explicit finite tables with compilation certificates; it is not a fresh admissibility oracle.

### 1.2 Exact boundary alignment with the physical world

Fix a finite immutable world X. It is an opaque nominal wire, not a collection of freely readable gate inputs. Let A be the readable input payload and Y the readable output payload. For compositional fixed-world synthesis use

    B=X×A,  C=X×Y.

Every physical event has the same X coordinate at both ends. Structural events with unequal world coordinates cannot have a physical lift and will be rejected. An equivalent presentation works in finite sets over X, but every shared-environment product must then be the product over X. One must not silently substitute it for an ordinary Cartesian product in an existing crossing schema.

A reduced one-shot target X←T→Y can be tested using its explicitly lifted form X←T→X×Y. Discarding X is allowed at a terminal observation boundary, not before later computations that still require the snapshot. A component originally specified on some different B is NOT identified with X×A merely because its underlying cardinality matches. It needs a supplied nominal boundary translation, verified on the event tables and compiled if used physically. The theorem applies only after this alignment has been established.

### 1.3 Finite hardware grammar

The physical input comprises:

* finitely many nominal readable sorts and protected sorts;
* a finite deterministic gate library, including only explicitly permitted constants and any abort operation;
* finite sensor primitives with actual finite execution-record sets and source/observation maps;
* a finite allocation grammar: bounded named acquisition slots, permitted primitive/receiver choices, and explicit sharing of a slot across wire uses;
* the nonadaptive eager immutable-snapshot convention: every installed acquisition executes once against the same X, independently of decoder outputs; no conditional acquisition, feedback, or implicit repeated sensing;
* finitely many permitted chart-wrapper templates, as described below.

For allocation a, let W_a be its synchronized record carrier including x, the readable input a_0∈A, and one record for each distinct acquisition vertex. Its source is (x,a_0). Its observation map exposes only the authorized local-state reads, a_0, and returned sensor values. Let H_a be the gate tables generated by finite typed saturation, retaining a circuit derivation for each table. For h∈H_a define

    C_(a,h)={w∈W_a : h(obs_a(w))≠abort},

with target (x,h(obs_a(w))). In a total apparatus omit abort and retain every W_a record. Gate-table saturation and snapshot normalization are proved in the implementation note: these enumerate exactly the semantic capabilities of this declared grammar, not all circuit layouts.

Set N=max_a |W_a|, with N=0 if the allocation list is empty; an empty allocation LIST means there is no implementation, not a zero-event implementation. An empty sensor allocation within the list is a legitimate apparatus and still has its input/world records.

### 1.4 Compiled adapters and actual record comparison

Each chart wrapper has one MARKED invocation of the common core device, explicit readable/opaque boundary types, and bounded additional acquisition slots. Independent invocations have different slots; shared acquisitions have one literal vertex. A finite template fixes the marked occurrence, receiver placements, deterministic processing regions, and admissible wiring. All extra acquisitions remain eager snapshot reads; no decoder branch suppresses them. Region inputs contain only the explicitly declared readable payload, local reads and acquired values, never an implicit projection of the opaque X. Each deterministic region is filled by the finite tables generated from its permitted inputs and gates. Template execution retains every primitive record and carries the same X throughout.

Thus the finite family of wrapper capabilities is generated from primitives and compilation certificates. It is not an oracle predicate on semantic maps. Its actual record carrier R_i and map

    ρ_i:R_i→C_(a,h)

are computed by evaluating the finite execution tuples and restricting each tuple to the marked core invocation. An asserted map ρ_i without that execution derivation is inadmissible. Reusing a core output preserves its one record; a second core invocation cannot be disguised as an adapter with one marked occurrence.

Let b_i:R_i→E_i be its actual local endpoint-profile map. Require

    boundary_core ρ_i = p_i b_i,                     (2)

and require the derived map

    (b_i,ρ_i):R_i→E_i×_E C_(a,h)                     (3)

to be bijective. This is the executable adapter's EXACT cartesian comparison. Extra hidden adapter executions fail injectivity unless the prescribed profile pullback itself demands those distinct representatives; missing executions fail surjectivity. If the intended interface change is only a more general span composition, it must be modeled as such rather than falsely labelled a cartesian restriction.

The snapshot-normalization completeness claim applies to snapshot wrappers too: every extra acquisition is eager and reads only its declared part of immutable X. An output inverse-fibre enumerator reading a computed output lies outside that restricted acquisition grammar unless separately supplied as an allowed finite primitive/template with a proved execution semantics. It can be included as a finite certified wrapper capability, but is not manufactured by assuming every inverse image is physically available. No completeness for arbitrary adaptive adapters is claimed.

## 2. Integrated finite bound

For an exact physically lifted global component T, event preservation gives

    |T|=|C_(a,h)|≤|W_a|≤N.                            (4)

Since T_i must be the actual pullback along p_i,

    |T_i| = Σ_(t∈T) |p_i^{-1}(boundary(t))|
          ≤ m_i N ≤ |E_i|N,                         (5)

where m_i=max_(e∈E)|p_i^{-1}(e)|, taking m_i=0 for an empty image/domain. More finely, each local fibre over z contains exactly |T_(p_i(z))| events. The bounds follow from physical records and exact interface coverage, not an arbitrary search cutoff.

Consequently even the doubly invisible sectors of the local all-fibres classification have bounded cardinality in this problem. Their automorphisms are not discarded; they are enumerated at the bounded sizes. Arbitrarily many gate vertices cause no unbounded semantic search because the finite table closure supplies their normal forms. Arbitrarily many acquisition vertices WOULD destroy (4); they are excluded by the finite hardware grammar. No resource pruning may delete an eagerly executed but output-unused nondeterministic acquisition: its records still contribute to W_a. Comparing allocations by output tables alone is unsound; any permitted pruning must preserve the exact event span and all actual record anchors. Deterministic raw-pin caching is a special case only under its explicit unique-record semantics.

## 3. Unified construction

The following procedure uses no assumed compatible local solution.

1. Generate every core allocation/table capability and its circuit certificate. Generate the permitted wrapper capabilities with their actual core-record restriction maps. Retain only the exact comparisons (2)–(3).
2. For each i enumerate the local component event counts up to (5), the endpoint-typed finite carriers, and all candidate factorization bijections α_i,β_i. Check (1) against the actual θ_i. This is the bounded specialization of the local all-fibres classification in `../foundations/Crossing_Grid_All_Fibres_Classification.md`, including all empty sectors. A failed local chart contributes no candidate.
3. For every tuple of local candidates derive the actual whole-event and required parent-event anchors. Form their least equivalence relation F on X_0=⊔_i T_i. Reject type conflicts and forced collapse of two distinct events at one local boundary lift.
4. Enumerate coarsenings K of F. Require type constancy, and exactly one element from each local fibre over every lift of the class's global type (A1–A4). If operations are part of the model, impose the derived congruence and no-imported-domain conditions O1–O2, with explicit operation graphs. Construct T_K=X_0/K and its local factorization maps; do not merely assert they exist.
5. Match one T_K to ONE core record carrier by a boundary-preserving bijection

       φ:T_K≅C_(a,h).

   For each chart use its quotient map k_i:T_i→T_K and demand a bijection φ_i:T_i≅R_i satisfying

       ρ_i φ_i=φ k_i,   b_i φ_i=e_i.                 (6)

   Under (3), φ_i is in fact uniquely forced by φ and k_i: invert (b_i,ρ_i). Check any additional supplied actual record anchors and operation interpretations, not just endpoint counts.
6. Output the quotient component, the original local maps transported through its exact restrictions, one core circuit certificate, wrapper certificates, φ,φ_i, and the verified finite comparison tables.

The principal version is generated: every global event lies in some k_i(T_i). Equivalently a successful core has no event whose boundary type is absent from all images p_i. If completely unobserved global hardware events are desired instead, they must be retained explicitly, not erased by quotienting. Such ungenerated extensions are OUTSIDE the present theorem, including its hardware-first variant below. They would require a separate specification of the extra records and of any operations connecting them to the observed part; they must not be silently truncated.

### Theorem 1 (integrated finite lifting and certificates)

For the finite input and generated component semantics just specified, the procedure terminates. It accepts exactly when there is one permitted snapshot-core implementation, permitted exact chart adapters, and local witnessed crossing factorizations of the given parents and actual whole matchings, all realized by that same core with the required actual event identifications. Every acceptance supplies compilation and factorization witnesses. A rejection means no such implementation exists within this exact declared grammar and hardware bound.

**Soundness.** Step 2 verifies the actual local crossing equations. A1–A4 construct the quotient T_K and bijections T_i≅E_i×_E T_K; substitution of these bijections into α_i,β_i preserves (1). O1–O2, where relevant, make these isomorphisms of partial algebras, including operation definedness. Step 5 identifies T_K with the actual core execution carrier, not merely its support. The wrappers are compiled primitives, and (3),(6) identify their actual records with exactly the required restrictions. Therefore every chart sees the same core event whenever the actual anchor requires it. Distinct local events at one lifted interface remain distinct. The stored gate derivations and template certificates are implementations of these exact execution tables.

**Completeness.** Any realization in the declared grammar normalizes to one of the finite core allocation/table capabilities without changing acquisition identities, record multiplicities, or sharing. The same normalization applies in every admitted snapshot-wrapper template; separately certified wrapper capabilities are already finite input. Its local restrictions have sizes bounded by (5), so Step 2 includes isomorphic copies of their local carriers and factorization maps. Their actual core-record equality defines K. It contains all derived anchors, satisfies A1–A4 by exact cartesian restriction, and satisfies O1–O2 by exact operational restriction. Generatedness identifies the whole core carrier with the quotient. Its physical record identification and normalized wrappers therefore pass Steps 5–6. All searches are finite: bounded finite carriers, finite bijection and partition sets, finite table closures, and finite template executions. ∎

This is not a claim that nested finite enumeration itself is a new mathematical mechanism. The content needed for the comparison is the hardware-derived bound on formerly unbounded sectors, the primitive derivation of K, exact coverage under noninjective interfaces, and the single execution-record comparison across all charts.

## 4. Equivalent hardware-first construction

There is a useful cross-check which avoids constructing local count vectors that cannot match any hardware. Start with a generated core C_(a,h). Its potential local carriers are determined exactly:

    T_i^phys = E_i×_E C_(a,h).

Enumerate the endpoint-compatible α_i,β_i on these carriers and test (1) and every actual whole/parent anchor. Test the compiled adapters through (3), together with all supplied physical record anchors. If operations are specified, check the exact local tables on these carriers.

### Proposition 2 (comparison of the two procedures)

The accepted semantic capabilities of the hardware-first procedure and the structural-first procedure are equivalent, including their event-identification data.

**Proof.** A structural-first acceptance sends t_i to (e_i(t_i),φ k_i(t_i)); A1–A4 and bijectivity of φ make this an isomorphism to T_i^phys. Conjugate α_i,β_i by it to obtain a hardware-first acceptance, preserving every actual anchor and wrapper equation. Conversely a hardware-first acceptance defines K on the tagged local carriers by equality of the common physical core record. Generatedness makes X_0/K≅C_(a,h), and exact fibre pullbacks give A1–A4. The accepted operations give O1–O2. These constructions undo each other up to the unique prescribed chart/core isomorphisms. ∎

In particular, local physical compilations with different hidden record identifications cannot pass merely because their endpoint supports agree. The hardware-first procedure uses one literal core record carrier in EVERY chart. This is the operational meaning of the quotient comparison, not an assumed descent theorem.

## 5. Semantic-capability groupoid and retained symmetries

Objects comprise the accepted local realization data, quotient K, a finite hardware capability (allocation and generated reachable decoder table), wrapper capabilities, and the exact identifications φ,φ_i. A circuit derivation is retained as an existence certificate, not counted as a distinct semantic capability every time redundant gates are inserted. Tables are identified on reachable observations only AFTER a genuinely generated full-table extension has been found.

With named hardware ports and records fixed, a morphism consists of local structural isomorphisms preserving every supplied parent/whole map and required operation, together with their induced quotient isomorphism g, such that

    φ′g=φ

and the corresponding chart record diagrams commute. The allocation and the physical semantic tables are fixed by such a morphism. If hardware symmetries are intended, their finite port/record actions must be explicitly specified by the device grammar and included in this equation; arbitrary permutations of physical executions are not free.

Before physical identification the structural classification is the action groupoid Adm//∏Aut(T_i,α_i,β_i,...), over bounded local representatives. The physical classification is its groupoid of compatible compiled record identifications, not a quotient that discards those identifications. Fixing all actual physical records can remove structural automorphisms; allowing certified hardware symmetries can retain them. These are symmetries of witnessed denotations, not of the infinitely many possible circuit layouts.

The equivalence in Proposition 2 is an equivalence of these groupoids: conjugating through the explicit pullback identifications preserves exactly their morphism equations. This is a precise semantic-capability classification with compilation witnesses, not an unsupported syntax-level classification.

## 6. Whole-system conclusions and permitted operations

### 6.1 When the surrounding whole is reconstructed

The basic theorem certifies one common component across supplied crossing charts. It does NOT automatically assemble the complete fixed W into one globally implemented surrounding network.

For a whole-factorization conclusion require the endpoint-cover hypotheses of structural Proposition 3: the local parents and fixed surrounding spans are actual restrictions of the global ones, the covering family includes every relevant input/output fibre, unchanged context witness coordinates agree, and ALL shared parent events contribute anchors, including parents invisible to W. Then α and the dual β are constructed by fibrewise cover gluing. Require the θ_i to cover the whole and agree as actual maps on overlaps; their global equation follows pointwise.

For a whole-EXECUTION conclusion additionally provide compiled implementations of all other components and contexts, with their actual record identifications and permitted wiring. Semantic parent specifications alone are not compiled devices. Under these conditions the circuit execution lemma transports the structural factorization equations to endpoint-preserving bijections of actual whole-network executions. This is equality up to specified execution isomorphism, not equality of circuit syntax or proof that arbitrary desired behavior can be implemented.

### 6.2 Substitution with correct sharing

In the unbounded acyclic snapshot language, serial substitution of compiled components on complete matching interfaces X×A, and parallel composition over the same X, is sound. The execution record is the corresponding pullback, respectively fibre product over X. Substitute ONE core occurrence by its certified circuit and retain its one set of acquisition records. If two occurrences invoke it independently, rename their acquisition vertices apart. If two charts refer to one actual occurrence, they restrict the same records; they do not run two independent copies and equate their visible answers afterward.

The grammar remains nonadaptive under these substitutions only when every acquisition still reads its declared part of the immutable snapshot and no decoder output chooses an acquisition. Resource bounds accumulate according to the resulting acquisition graph. Therefore the fixed finite apparatus is NOT claimed closed under substitution: after composition its allocation must belong to the permitted enlarged grammar, or the finite lifting test must be rerun with the actual new resource bound.

### 6.3 Exactly which restrictions are physically available

A deterministic compiled input adapter, with one execution per new input and the required nominal visibility, realizes the corresponding input restriction. A nondeterministic adapter with additional records realizes span composition instead; one must test (3) rather than erase its multiplicities. Output pullback along a noninjective function requires the prescribed inverse-fibre executions. It is available only when an explicit certified fibre-enumerator primitive/wrapper (or an equivalent synthesized capability) produces exactly those records. Mathematical finite-span restrictions alone do not supply it.

Structural simultaneous base change transports K coherently as proved in Proposition 4 of the structural note. A PHYSICAL transported solution exists only for compiled adapters passing the exact record comparison and fitting the resulting acquisition allocation. When they exist, associativity of record restriction and the complete-interface execution bijections show that the transported chart diagrams agree under canonical tuple reassociation. Two independently chosen adapter paths with different hidden records need not give the same physical realization merely because their underlying boundary functions are equal.

### 6.4 Positive equipment consequence for certified interfaces

The companion `../implementation/Maximal_Permitted_Interface_Equipment.md` proves a positive structure theorem. Let H be the endpointwise replete semantic image of the UNBOUNDED finite snapshot circuit language in spans over X. Let V_H contain exactly the nominal boundary functions f for which both the forward graph span f_* and the converse span f^* have actual circuit certificates with exact records. Then H, V_H and all compatible ambient semantic span cells form a virtual equipment. Its restriction compiler is f_*;T;g^*, with actual records (a,t,d) satisfying the two endpoint equations.

This is the largest class of actual vertical functions for which the SAME H supports all ambient cartesian restrictions: restricting units forces both certificates. Cells here are semantic witness maps, not automatically executable transformations of circuit layouts. The result supplies a principled positive source of exact wrapper templates for the finite lifting theorem. The finite allocation bound still has to accommodate their actual acquisitions; the bounded fibre need not be composition-closed; no such closure is asserted. Membership in the unrestricted semantic image is not declared decidable by the bounded algorithm.

## 7. Concrete discriminating cases and remaining scope

The companion endpoint-Cartesian active cycle family has locally correct crossing charts but no joint structural quotient; it fails before synthesis. Its positive control passes that stage. The implementation note's active four-component AND grid has a unique coherent structural reconstruction and locally executable affine restrictions, but no common affine-gate implementation; it fails the hardware table test. Adding the AND gate repairs it. These failures occur at different stages of this one theorem and neither is inferred from the other.

Established scope: a designated common component, a finite family of witnessed crossing charts, explicit arbitrary boundary-profile maps filtered by actual compiled adapters, finite hardware, and nonadaptive snapshot circuits. The finite search includes the previously unbounded local invisible sectors, with a justified cutoff. It does not establish arbitrary feedback/controller synthesis, unrestricted adaptive sensing, reconstruction of every unknown component at once, or a physical equipment over all finite boundary functions. The certified relative equipment of §6.4 is established; fixed-budget closure is not. Standard gluing, finite term-function saturation, and permutation holonomy remain acknowledged baselines. No novelty-priority or Lean-verification claim is made.
