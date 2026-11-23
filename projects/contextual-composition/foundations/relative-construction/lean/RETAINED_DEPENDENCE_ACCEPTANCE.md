# Retained dependence and native assembly

The mathematical targets for issue [#101](https://github.com/eternal-november/eos-research-programmes/issues/101) are the named results below in the roadmap's source snapshot at `458ff36a4798e432dee5947afc402f9903a47f14`. Lean names in the tables start inside `ContextualComposition`. Each row identifies what the declarations certify and which hypotheses a later application must supply. The theorem index records individual declarations for the package axiom audit.

## Joint admission and retained reassociation

| Source judgment | Lean declarations | Scope |
| --- | --- | --- |
| Tree admission, equation (E) | `TreeOverlapAdmission.ofEdges`, `attach_leaf`, `necessary`, `admission` | For an arbitrary finite nonempty simple tree, arbitrary vertex and edge sets and endpoint maps, edge compatibility is equivalent to existence of a joint effect on the subtype of all matching vertex tuples. The induction removes an actual degree-one vertex. The only functorial exactness hypothesis is surjectivity of each canonical pullback comparison. |
| Exact retained reassociation | `RetainedTreeReassociation.DataAt`, `data_determined`, `full_root_equivalence`, `retains_root`, `reassoc_trans`, `reassoc_pentagon` | Both child laws are stored and constrained by their parent. The complete root law determines them. The construction works for any binary partition into singleton leaves and therefore covers every connected-subtree splitting in the source. Its carriers are fixed compatible-tuple sets. Arbitrary redundant witness presentations lie outside this equivalence. |
| Native diagram maps | `RetainedTreeReassociation.DiagramMap.mapData`, `reassoc_natural`, `TreeOverlapBoundaries.retained_identity`, `retained_comp` | Vertex maps and commuting boundary maps send every stored law to the appropriate new raw carrier. The target vertex effects must be the pushed source vertex effects. |
| Limits of local compatibility | `TreeOverlapBoundaries.cycle_matches`, `cycle_no_joint`, `dead_joint`, `dead_projection`, `ProbabilityOverlapBoundaries.cycle_agreement`, `cycle_no_distribution`, `zero_weight_dead` | The triangle of equality, equality and inequality has locally agreeing marginals and an empty tuple carrier. A compatible single edge can also have an unliftable raw point. Separate constructions establish these statements in nonempty powerset and normalized probability. |

[Tree admission and retained reassociation](../../retained-dependence/Tree_Overlap_Admission_and_Retained_Reassociation.tex)

## Composition, wiring and local products

| Source judgment | Lean declarations | Scope |
| --- | --- | --- |
| Associative relational composition | `AllCouplings.Comp`, `glue`, `associative`, `nonblocking`, `CouplingChains.assoc`, `left_unit`, `right_unit`, `Chain.possible_iff_joint` | A ternary effect realizes the two input couplings and the specified output coupling. Both bracketings admit precisely the same outer laws. The length-zero chain gives the diagonal and arbitrary finite chains retain their prescribed adjacent marginals. |
| Information loss under state maps, equation (L) | `CouplingChains.change_lax`, `change_identity`, `changeEquiv`, `change_iff`, `CouplingHiding.hiding_strict`, `ProbabilityOverlapBoundaries.hidden_all`, `strict_hiding` | Deterministic law-preserving maps transport existing triples. State isomorphisms identify the hom types and both composition relations. Erasing a shared bit admits the full possibility relation or the independent fair-bit law with unchanged endpoints. |
| Exact uniqueness boundary | `CouplingPullbacks.map_injective`, `quad_surjective`, `exact_uniqueness_boundary`, `CouplingPossibilities.quadrilateral_failure`, `FairBitNativeMultilimit.quadrilateral_failure` | Under weak pullback preservation, bijective quadrilateral comparison, bijective binary comparison over the terminal effect, uniqueness of every compatible binary coupling and preservation of all pullbacks are equivalent. Distinct effects on the same raw pair distinguish the two concrete failures. |
| Coherent hierarchical wiring and representability | `ConeWiring.substitute_assoc`, `unit_outer`, `unit_inner`, `permute_subst`, `transport_subst`, `reindex_comp`, `representable_iff_product`, `ConeRepresentability.finite_iff`, `unary_tensor`, `unary_unit` | An operation is a complete family of maps from the given root to its components. Substitution composes the actual projections. A natural representation of each finite cone functor is equivalent to the corresponding product universal property, including the terminal object in arity zero. The resulting tensor on the opposite unary category uses the original products. |
| Dependent serial interchange, equations (L) and (A) | `DependentConeInterchange.assemble`, `interchange`, `extension_interchange`, `cone_substitution`, `reindex_assemble`, `assembled_triangle`, `associate_natural`, `leftUnit_natural`, `rightUnit_natural` | For a Set monad the second native map is indexed by the actual first joint witness and targets the effect at its projected component witness. The two substitutions agree on the full dependent pair, its pushed effect and the extension map. |
| Local-to-global cone assembly, equations (C) and (P) | `NativeOperationAssembly.conditional`, `Square.horizontal`, `jointSerial`, `horizontal_vertical`, `serialCell_comp`, `serialCell_id`, `associate_horizontal`, `triangle`, `pentagon`, `finite_assembly` | First-stage body compatibility transports the second carrier to its actual component input. The output preserves the entire joint body and every native projection. Finite chains may change both the joint and the component interfaces. Cells include effect and body preservation. These serial results use the monad laws. Arbitrary separately chosen continuations require their own conditional maps. |
| Products in the original native comma presentation, equations (1) and (2) | `NativeCommaProducts.Grades`, `Lift`, `ofPullback`, `uniqueLift`, `productLimit`, `NativeCommaReindex.transportedLift`, `mappedProduct`, `NativeSpanProducts.domain_cartesian`, `equivalence`, `terminalIsTerminal`, `NativeSpanBaseChange.beckChevalley`, `preservesNative`, `finiteGrades`, `hasFiniteSpanProduct` | The construction consumes actual context, content and base product cones. The base pullback and the specified cartesian lift along the context extension determine the unique native factor. Pure-input transport additionally consumes grade-product preservation, lift preservation and the pullback naturality square at the lift. The all-maps slice example proves those conditions using actual apex maps and recovers the terminal span over the product of the endpoints. A restricted class requires its own checks. |

[Relational composition and hiding](../../diagram-native-interaction/Relational_Composition_of_All_Couplings.tex), [quadrilateral uniqueness](../../diagram-native-interaction/Unique_Quadrilateral_Filling_and_Dependence.tex), [hierarchical wiring and dependent interchange](../../retained-dependence/Multicategorical_Coupling_Wiring_and_Context_Interchange.tex), [conditional assembly](../../retained-dependence/Native_Coupling_Cones_and_Conditional_Assembly.tex), [original comma product criteria](../../shared-witness-interaction/Products_in_the_Original_Native_Comma_Presentation.tex)

## Dependence, completion and selectors

| Source judgment | Lean declarations | Scope |
| --- | --- | --- |
| Marginal-only naturality, equation (N) | `FiniteProbabilityLaws.distribution`, `NaturalMarginalCouplings.corner_add`, `IntervalAdditivity.linear`, `NaturalMarginalCouplings.independence`, `diagonal_forbidden`, `IndependentProbabilityProduct.family`, `unique_family`, `independent_fails_product` | The input distributions have finite support and arbitrary nonnegative real weights on arbitrary sets. The two maps in naturality vary independently. Three indicators applied to one normalized joint law give interval additivity. Positivity and rational density suffice to force multiplication of all point masses. The independent family realizes the laws. A product of fair-bit objects in the native deterministic-map category would force every coupling to be one joint law. Diagonal and independent couplings contradict that requirement. Same-map-only naturality has a different scope. |
| Native multilimit | `NativeMultilimits.nativeHom`, `multilimit`, `factor_natural`, `no_index_no_cone`, `emptyIndex`, `NativeCoefficientLimits.coefficients`, `baseCone`, `baseIsLimit`, `nativeTupleMultilimit` | The tuple set satisfies every diagram equation. At each tuple the coefficient objects and transported coefficient arrows form an actual diagram. Its chosen limit supplies the unique coefficient factorization. The disjoint index is the whole set of compatible effects. Precomposition by a native arrow preserves the induced index. The empty diagram admits every effect on its terminal raw carrier. An empty index precludes every cone. |
| Conservative finite assembly completion | `NativeMultilimits.singletonFullyFaithful`, `NativeFamilyCompletion.isLimit`, `native_family_finite`, `singletonIsLimit`, `NativeMultilimitComparisons.indexMap`, `transition_projection`, `transition_id`, `transition_comp`, `missing_index`, `FairBitNativeMultilimit.indices`, `interval_components`, `completedLimit` | A map of small families chooses one target index and one full native morphism per source component. Finite coefficient limits suffice for finite limits of this family category. The explicit family is the limit of the diagram of singleton families. An entire real interval injects into the components for two fair bits with terminal coefficients. Diagram maps push the joint law and carry coefficient arrows. The cone of an omitted index witnesses the loss of universality for the full native category. |
| Dependent selector obstruction | `DependentSelectorObstruction.fixed_continuation`, `erasure_preserves`, `no_body_square`, `source_law`, `different_output_laws` | Each fixed singleton continuation survives erasure. Selecting the input bit as its own returned index yields a fair output. Each fixed target-family index yields a constant. No map on the entire raw witness pair can commute with those outputs. Finite assembly completion alone supplies no transport for that selector. |

[Naturality of marginal-only coupling](../../retained-dependence/Naturality_Obstruction_to_Marginal_Only_Dependence.tex), [native multilimits, completion and selectors](../../native-multilimits/Native_Multilimits_and_Selector_Obstruction.tex)

## Joint occurrence admission and prefixes

| Source judgment | Lean declarations | Scope |
| --- | --- | --- |
| Exact local admission and constructed body | `JointOccurrenceAdmission.bodyEquiv`, `canonicalStep`, `necessary`, `admission`, `JointOccurrenceSystem.jointSystem`, `componentMap`, `global_admission` | Full boundary occurrence effects include both shape and addressed positions. Connectedness forces one common shape. The constructed body reads every position of each matching raw tuple. Its effect comes from tree admission. A state-indexed system uses a supplied family of lifts, or ordinary choice when only their pointwise existence is given. |
| Joint native prefix system | `OccurrenceFubini.productFin_natural`, `discard`, `OccurrenceFubiniPermutation.exchange_iff`, `frontier_product_eq`, `GuardedOccurrencePrefixes.prefixMap`, `prefix_truncate`, `truncate_map`, `flattened_prefix_map`, `JointPrefixRealization.frontier_chart`, `joint_native_prefix_system` | The frontier uses a finite product of conditional effects. Ordinary commutativity removes the enumeration choice. Bind threads the actual retained history through the polynomial positions. Affinity makes last-layer forgetting effect-preserving. Native projections preserve the complete addressed body at every finite depth and its natural flattening when that operation is supplied. |
| Conditional raw inverse-limit lifting | `RawOccurrenceLifting.frontier_reachable`, `extend_lift`, `raw_limit_surjective`, `JointPrefixRealization.joint_raw_lifting` | Surjectivity is required on the raw witness map at every reachable state from the specified joint root. Successive lifts extend the already chosen prefix, giving a compatible sequence by choice. The result concerns raw inverse sequences. |
| Two explicit effect models | `CouplingPossibilities.weak`, `NonemptyPossibilityMonad.monad`, `affine`, `exchange`, `ProbabilityPullbackGluing.row_total`, `col_total`, `on_pullback`, `weak`, `FiniteProbabilityMonad.monad`, `bind_eq`, `affine`, `exchange`, `JointPrefixRealization.probability`, `possibility` | Nonempty possibility uses direct image and union. Normalized real finite-support distributions use finite mixture. The latter's weak comparison assigns a matched pair mass equal to the product of its two weights divided by its boundary mass, with zero contribution at zero boundary mass. Both constructions retain the full raw carrier. |

[Boundary-admitted joint occurrence unfolding](../../joint-occurrence-unfolding/Boundary_Admitted_Joint_Occurrence_Unfolding.tex)

## Verification and scope of downstream use

From this package, `lake build` checks the modules exported by the package root and `lake env lean AxiomAudit.lean` prints the indexed declaration axioms. The package verifier combines both with the theorem-index and axiom-allowlist checks. The pin is Lean 4.35.0 with mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. A module replay certifies the replayed declarations and imports. A clean package-build claim requires the build receipt for the integrated revision. Manuscript proofs and historical finite Python diagnostics have distinct evidence status.

Application to an independently constructed crossing under #92–#94 requires the declarations and hypotheses of that particular crossing. Shared-state actions require the verified pure-input maps or separate product-preservation evidence. Output transport has the directed comparison supplied by its projections. Stronger synchronization remains conditional on output exactness. The family limit theorem is static. Witness-dependent continuation selection, guarded scheduling, physical coupling identification, infinite probability measures and fairness require additional data and laws appropriate to each claim.

## Module dependency order

The rows are in topological order. Each right-hand cell gives every directly imported project module. The separate finite-writer obstruction supplies the probability kernels used by the selector example. Mathlib imports are specified in each module.

| Module | Direct project imports |
| --- | --- |
| `CouplingPullbacks` | — |
| `DependentSelectorObstruction` | `FiniteWriterObstruction` |
| `IntervalAdditivity` | — |
| `NativeCommaProducts` | — |
| `NativeMultilimits` | — |
| `AllCouplings` | `CouplingPullbacks` |
| `CouplingPossibilities` | `CouplingPullbacks` |
| `NativeCommaReindex` | `NativeCommaProducts` |
| `NativeFamilyCompletion` | `NativeMultilimits` |
| `NativeSpanProducts` | `NativeCommaProducts` |
| `CouplingChains` | `AllCouplings` |
| `NativeCoefficientLimits` | `NativeFamilyCompletion` |
| `NativeMultilimitComparisons` | `NativeFamilyCompletion` |
| `NativeSpanBaseChange` | `NativeCommaReindex`, `NativeSpanProducts` |
| `TreeOverlapAdmission` | `AllCouplings` |
| `ConeWiring` | `CouplingChains` |
| `CouplingHiding` | `CouplingChains`, `CouplingPossibilities` |
| `JointOccurrenceAdmission` | `TreeOverlapAdmission` |
| `RetainedTreeReassociation` | `TreeOverlapAdmission` |
| `ConeRepresentability` | `ConeWiring` |
| `DependentConeInterchange` | `ConeWiring` |
| `FiniteProbabilityLaws` | `ConeWiring` |
| `JointOccurrenceSystem` | `JointOccurrenceAdmission` |
| `TreeOverlapBoundaries` | `CouplingPossibilities`, `RetainedTreeReassociation` |
| `NativeOperationAssembly` | `DependentConeInterchange` |
| `NaturalMarginalCouplings` | `FiniteProbabilityLaws`, `IntervalAdditivity` |
| `NonemptyPossibilityMonad` | `CouplingPossibilities`, `DependentConeInterchange` |
| `OccurrenceFubini` | `DependentConeInterchange` |
| `GuardedOccurrencePrefixes` | `JointOccurrenceSystem`, `OccurrenceFubini` |
| `IndependentProbabilityProduct` | `NaturalMarginalCouplings` |
| `OccurrenceFubiniPermutation` | `OccurrenceFubini` |
| `FairBitCouplingFamily` | `IndependentProbabilityProduct` |
| `ProbabilityPullbackGluing` | `IndependentProbabilityProduct` |
| `RawOccurrenceLifting` | `GuardedOccurrencePrefixes` |
| `FairBitNativeMultilimit` | `FairBitCouplingFamily`, `NativeMultilimitComparisons`, `ProbabilityPullbackGluing` |
| `FiniteProbabilityMonad` | `DependentConeInterchange`, `ProbabilityPullbackGluing` |
| `JointPrefixRealization` | `FiniteProbabilityMonad`, `NonemptyPossibilityMonad`, `OccurrenceFubiniPermutation`, `RawOccurrenceLifting` |
| `ProbabilityOverlapBoundaries` | `FiniteProbabilityMonad`, `TreeOverlapBoundaries` |
