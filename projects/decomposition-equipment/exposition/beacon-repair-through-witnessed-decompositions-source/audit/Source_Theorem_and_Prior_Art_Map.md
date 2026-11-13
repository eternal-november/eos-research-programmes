# Beacon application: exact machinery and strongest-baseline audit

2 November 2026. Bounded application audit, not a new contract, novelty finding, or physical beacon certification. Sources were read directly; public primary sources were freshly checked. The source paths below identify precisely which old statements are being reused.

## 1. The useful core and what it does not prove

The proposed finite network has occurrence-labelled components N,P,Q,S. N negates the shared control g; P and Q have the same board type B(d,c)=d∧c, but P is wired to N(g), Q to g. The output path is a→P→Q→y and the safety check S requires g=0. Mission: y=a for both Boolean inputs and S=1. The two boards individually pass their identity test at local control 1. Pulled back along their actual wiring maps, their good-mode sets are L={0} and R={1}. Thus the actual joint witness set L×_{M}R, M={0,1}, is empty. Forgetting M before joining gives L×_*R, a singleton. The canonical comparison is the unique map ∅→{*}, not an isomorphism. This is a complete tiny instance proof; it assumes neither compatibility nor a mysterious categorical obstruction.

An inverter at Q's control changes the whole network and makes both constraints g=0. An inverter at P instead makes both g=1, violating S. Thus identical board types do not make occurrence-specific repair decisions interchangeable. Opening a box reveals a decomposition of the same whole; inserting the inverter is a replacement and must not be mislabeled same-whole refinement.

The elementary constraint solver is standard relational natural join. Keeping full tuple witnesses, named occurrences, graph whole, seam maps, and every intermediate certificate permits a stronger *representation* claim than merely checking the final Boolean answer. It does not establish a stronger solving algorithm than relational CSP/database methods.

## 2. Exact old theorem map

### E2: actual cells and presentation recovery — directly usable

Source copied as `E2_reconstruction_reference.md`, original `e2_presentation_reconstruction_delivery_20261031/source/reconstruction_theorem.md`, §§1–2 (especially §2.3).

A cell in V(N,M) is (π,φ,m): an actual ordered partition of a retained whole graph, an endpoint-compatible map from the full composable witness tuple P(p) to an actual target span apex, and a monoid scalar. Use scalar monoid {1}. Set/span objects, actual leg maps, whole edge relation and tuple flattenings are supplied data. E2's normal form is a flat cut followed by the actual unary span square, so a beacon assembly with explicitly tabulated φ is genuinely representable by the old local generators. This is not recovery of unknown electrical semantics from the word “component”, nor reconstruction of missing cross-edges from isolated parts.

Required application deliverable: list graph edges, partition blocks, span endpoints/apices/legs, and φ or its finite executable definition. A prose claim that relations form an equipment is insufficient. This use is P-level specialization; no new Lean formalization is inferred.

### E5: exact assembly and whole-diagram certificate transport — directly usable with tests

Source `reference_sources/decomposition/stage_sources/E5_exact_assemblies_transport_source/source/theorem.md` in the prior application recovery.

- Theorem 2.1: every retained named local map t_v must have exactly one preimage of each target witness. This is necessary and sufficient for the *whole retained staged diagram* to be coefficient-faithful. Root-only bijectivity does not suffice.
- Theorem 3.1: for fixed interfaces and exact proper cut maps β,β', stage comparisons are explicitly k_v=β_v P(k_children)(β'_v)^{-1}. An independently supplied root has to satisfy its own equation γ_new=γ_old P(k_children); it is not automatic. The formulas, not equal cardinalities, give coherent finite graft/contraction comparisons.
- Theorem 4.1: for restriction maps f_i, the canonical map from composing restricted spans to restricting the composite has fibre ∏ f_i^{-1}(a_i) over each feasible tuple. Exactness requires unique lifts at every named relevant run; units additionally require the diagonal A'→A'×_A A' to be bijective, i.e. f injective.
- §8: the retained whole and cross-edges are extra data, not inferred by coefficient exactness. Multi-nonempty-graph assemblies need not be opcartesian (Theorem 1.1 requires at most one nonempty graph entry).

The beacon's forget-then-join ∅→{*} is NOT literally Theorem 4.1's inverse-image restriction map. It is a direct finite-span/image comparison. Do not cite the restriction theorem with q:M→* in the wrong variance. A separate duplicated-seam 2→1 control can instantiate E5's theorem: it preserves existence but gives two lifts and therefore loses unique-witness exactness. This is an optional genuine stronger check, not needed to solve the beacon.

### D2: relation versus actual witness preservation — relevant distinction, not a variance shortcut

Copied `D2_reference.md`, original `d2_d3_interface_descent_delivery_20261031/source/d2/theorem.md`.

Theorems 2.1/3.1 give the support condition for *inverse-image restriction* of finite relational composition. Actual span isomorphism is stronger than relational equality; §6 gives retained-witness/all-tree criteria imported from CUT/I4. This supports precise naming of the observable level. The beacon forgetful-image comparison is proved directly and is not D2's theorem verbatim. Empty witness sets and retained endpoint sorts cannot be discarded.

### B3: occurrence-sensitive semantic refinement — directly relevant, with scope boundary

Source `reference_sources/decomposition/formal_sources/core/witnessed_decompositions/Results_Integrated_A4_C5_B3.txt`, introductory result and Parts I–III.

Each semantic refinement arrow retains a tuple of full evaluated operations at the *original source occurrences*, not only the aggregate output. Whole graph, ordered partition, full interface path and scalar remain in each entry. The independently presented graft/equation category compares soundly and completely to these tuples. P and Q may share a type but must remain distinct positions. The theorem does not imply that arbitrary physical replacement preserves the original whole; use a separate replacement map/model comparison with its actual boundary effect. Nor does semantic B3 retain every primitive stage of an arbitrary representative forest: a fully staged certificate claim must retain that extra record explicitly.

### I4: crossing cuts and substitution — use the negative test honestly

Source `reference_sources/decomposition/stage_sources/I4_cut_substitution_interchange_source/source/theorem.md`, §3.2A and §3B.

Physical cut ({N,P},{Q,S}) flattens to N,P,Q,S. Functional cut ({N,S},{P,Q}) flattens to N,S,P,Q. Their set intersections are singletons, but these are NOT the same ordered atom frontier. The old nonsymmetric calculus does not grant the needed permutation. I4's O test rejects treating this as an admitted planar rotation. Both cuts can still be separate actual cells over the same whole graph. An explicit coordinate-reindexing isomorphism of the labelled assignment sets can compare their semantics, but that is a separately proved bounded bridge, not an inherited planar-cut theorem. It should preserve all named coordinates and incidence equations, with inverse permutation exhibited.

If a second example of parallel regrouping is desired, use two parenthesizations of one fixed occurrence path. E5/I4 then apply directly and prove all retained stages, not only final truth-table equality.

### I1 and I5: informative but do not claim automatic instantiation

I1 source copied `I1_reference.md`, original `i1_amalgamation_delivery_20261031/source/conservative_amalgamation_theorem.md`, §§1–3. Its pushout theorem is for monoid-labelled occurrence enrichments P[L], in a specified category over the old graph theory. Its exact faithfulness criterion concerns coefficient monoid pushouts. Boolean good-mode sets and their empty intersection are not that construction. The beacon illustrates an analogous compatibility issue, but is NOT a fresh application of the I1 pushout theorem without an explicit monoid-presentation encoding.

Final corrected I5 source `reference_sources/decomposition/sources/full_unital_repair_20261101/modular/full_unital_modular_repair.md`, §§2–4. Joint witness matching glues when the full shared separator records and old cut skeleton agree. The theorem is for specified active-occurrence coefficient theories; completeness and optimality are separate, with extra unit-observation/reflection requirements for optimality. The beacon's exact shared-mode pullback is the corresponding elementary finite-instance proof, not a claim to inherit the entire coarsest repair theorem. Retaining g repairs this example's incorrect join verdict, but does not establish universal minimality of a learned observation doctrine.

## 3. Strongest primary baselines

### Relational database join and lossless decomposition — closest baseline

Beeri, Fagin, Maier and Yannakakis, *On the Desirability of Acyclic Database Schemes* (JACM 1983), [author institution record](https://research.ibm.com/publications/on-the-desirability-of-acyclic-database-schemes). The checked abstract explicitly relates acyclic schemas, join dependencies and equivalent structural characterizations. We did not verify a specific numbered full-text theorem, and do not attribute one. In this beacon, join constraints and the spurious result from erasing a shared variable are established database/CSP phenomena, independently proved above. No new general join or losslessness result is claimed.

Yannakakis, *Algorithms for Acyclic Database Schemes* (VLDB 1981), [publisher bibliographic record](https://www.vldb.org/dblp/db/conf/vldb/Yannakakis81.html). Direct PDF retrieval failed in this pass. Do not claim a newly verified complexity comparison or acyclicity theorem. The tiny model requires no performance claim.

### Component compatibility and refinement

de Alfaro and Henzinger, *Interface Automata* (FSE 2001), [primary paper](https://web.cs.wpi.edu/~heineman/html/teaching_/CS562/p109-de_alfaro.pdf). The paper treats compatibility of input assumptions/output guarantees and alternating refinement. Beacon is a static finite model, not a new dynamic/game-theoretic interface theory, and does not outperform this baseline.

Cobleigh, Giannakopoulou and Păsăreanu, *Learning Assumptions for Compositional Verification*, [primary NASA report](https://ntrs.nasa.gov/api/citations/20030017771/downloads/20030017771.pdf). The retrieved report is dated November 2002 (related conference publication 2003). It learns assumptions then discharges them against the environment using counterexamples. Merely learning which shared mode a subsystem requires is not a novel general principle. This application has no learning algorithm unless probes, hypothesis class and epistemic guarantees are supplied.

### Ambient categorical organization

Cruttwell and Shulman, *A Unified Framework for Generalized Multicategories*, [primary paper](https://arxiv.org/pdf/0907.2460v3), §§5 and 7. Composition/unit/restriction infrastructure belongs to established virtual-double-category/equipment theory. The old project's selected graph/span presentation and retained-certificate criteria provide an exact application language, not a new generic equipment framework.

## 4. Recommended claim and acceptance checks

Claim: a worked finite synthesis using actual graph/span assembly cells, occurrence-specific comparisons and retained joint certificates, with an explicit failure of seam erasure and an occurrence-sensitive repair. More of the older machinery is exercised than in the linear compensated-tool example, but familiar finite relational reasoning already solves the truth-table problem.

Acceptance checks: (1) original whole and two actual cut cells; (2) explicit E2 normal forms or maps; (3) all named witness maps and inverses where claimed; (4) crossing-order failure acknowledged; (5) replacement changes whole; (6) ∅→singleton failure; (7) fixed adapter at Q versus P; (8) any copied E5 theorem has its exact hypotheses; (9) no I1/I5 blanket application; (10) no hardware, arbitrary feedback, novel discovery or general efficiency claim.
