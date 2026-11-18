# Recovery and next bounded operation

The reviewed baseline is PR #162, archive SHA256 bd12e6d74374241f4897454a3adb5692d1f8f7c6e889040d50edce706ac8d86c, restored at contextad-lean. Lean release 4.35.0 was restored from the surviving release archive. Dependencies must match lake-manifest.json; prior build evidence is historical until replayed here.

Read contextad-lean/README.md and the final SOURCE_CROSSWALK.md section, then PrimitiveBalance.lean (localizationEquivalence), NormalizationCoherence.lean (the two actual endpoint squares), and mathlib CategoryTheory/Equivalence.lean (Equivalence.mk/adjointifyη). The next operation needs the packaged unit, not the pre-adjointification contraction: Equivalence.mk preserves the counit but adjusts the unit. Confusing these would silently prove a different theorem. Derive the packaged counit square from the source section comparison and factorization maps, then derive actual unit compatibility by faithfulness and triangles. Do not replace the actual squares or claim global factory coherence.

EquivalenceCoherence.lean is now an author-verified candidate, indexed and imported by the root. The baseline had 354 indexed declarations; the candidate has 359. Author build/axiom audit and a relocated fresh own-source replay both passed. Sequential independent scoped review and fresh own-source replay subsequently passed; the bounded result was merged in PR #163 at ff4c17c5de2d6435d728fe33f208562d91b1a7bf. Dependency binaries may be cached, but own project sources must replay. Re-read this route if the underlying equivalence definition, endpoint maps, or source pin changes.

## Next bounded candidate after #163

LocalizedCoconeTransport.lean connects the existing chosen localized transports to independent-cocone pullback/postcomposition. Read the final SOURCE_CROSSWALK section and LOCALIZED_COCONE_TRANSPORT_FREEZE.json. The source comparison is restriction along Q, and its endpoint component is G applied to the inverse of chosenLift.comparison. That direction is material: replacing it by an identity silently changes the chosen-transport square. The new declarations preserve every preceding implementation module, dependency/toolchain pin and verifier. Author build/audit and relocated fresh own-source replay passed 375 indexed declarations. Independent scoped review and fresh own-source replay passed; see evidence/localized-cocone-independent/Independent_Localized_Cocone_Review.tex. The next review must check the exact existing cocone compositors, target interchange and nonidentity localization comparison, not merely that the new equivalence exists. Composite-equivalence recovery-map modifications and full comma-route comparison remain explicitly unproved.

## Actual recovery candidate after #164
Baseline merge 24b033d725c0ffd3124aeb7ac6b974e7d8a82985. Read the last crosswalk section, the previous forward squares, EquivalenceCoherence.unit_square_of_counit and CoconeRecovery.lean. Verify that the concrete comparison is passed in the opposite direction to the general forward-square convention and that the actual composite record appears on both sides. Distinguish a single change from a pasting of changes, for which the correction isomorphisms are new obligations. Independent review passed; see evidence/cocone-recovery-independent/Independent_Cocone_Recovery_Review.tex and adjacent fresh replay records.

## Independently reviewed recovery modification after #165
Baseline merge 117cd3b66bb2d820d97c8201159b1b56c60c0e33. Read the final crosswalk, the #165 recovery component, #164 forward choice and target-transformation equations, and RecoveryModification.lean. Preserve the distinction between a noninvertible transformation of target functors and an invertible compatible endpoint choice. To extend this to horizontal transport composition, account for the cocone and localized compositors and mixed associators; the vertical law is not that equation.

## #105 finite telescope branch after #166
Read issue #105, source pin 458ff36a lines 929–953, scoping-audit lines 169–184 and proof-status ledger K2; #150 and #151 do not contain a telescope construction. Start at FiniteTelescope.Chain, not at the later #93 recovery modules. Check both flatten units, the triple law, pack/unpack inverses and payload naturality, and the two units' distinct domains. The degree-dependent witness and parallel grades are tests against a constant fibre or endpoint-only substitution. See FINITE_TELESCOPE_FREEZE.json, the final crosswalk and evidence/finite-telescope-author-fresh. The next extension to nondiscrete grade morphisms will require a morphism-of-chains interface, not merely more object examples.
Independent scoped review passed. See evidence/finite-telescope-independent, including a separate probe whose successor depends on the chosen grade.

## #105 telescope native-morphism branch after #167
Read the final two crosswalk sections, then ChainHom, chainCategory, singletonHomEquiv, flattenFunctor and the three homogeneous law statements in TelescopeMorphisms.lean. The casts use exactly the #167 equalities on old chain objects. Recover the noninvertible and parallel-map witnesses before considering constructions that quotient the hom family. For the Cat-valued extension comparison, define arrows in payload-bearing values and in iterates, then prove the equivalence on them; the old object equivalence is insufficient.

## Cat-valued telescope extension after #168
Read the pinned eq:telescope passage, the preceding two telescope tranches and the final crosswalk. TelescopeExtension.lean builds ValueHom and PackedHom independently on the earlier object types, before defining either comparison functor. Test a singleton with an arbitrary grade map and an arbitrary payload map, and check the no-cross-length and shared-next-state conditions. The strongest roundtrip statements are equalities of functors. To generalize to a nondiscrete base, simple equality of next states no longer describes all allowed transport; a real reindexing/cleavage interface is needed.

## Telescope payload 2-cell candidate after #169
Read the final crosswalk and eq:telescope at the pinned manuscript lines 929–953. Compare #169's forward_payload/backward_payload (individual payload functors) with forward_family/backward_family (functors on the parameter hom-category); do not conflate this vertical result with horizontal 2-functor data or base reindexing. The exact fixed-state reachable-endpoint criterion is a check against claiming each single fibre is faithful on all families. See TELESCOPE_PAYLOAD_CELLS_FREEZE.json and evidence/telescope-payload-cells-author-fresh.
Independent scoped review passed; see evidence/telescope-payload-cells-independent/REVIEW.md and its fresh own-project build and 543-declaration axiom audit. The nine pinned dependency build caches were reused.

## Telescope reindexing after #170
Inspect the typed output of Reindex.Split.lift before reading the recursion: the induced map between successors controls the next grade, and the final induced map restricts the terminal payload. Read pack_reindex, baseComparison, comparison_payload and the predicate example after the final crosswalk section. The earlier discrete-base category of chains does not define transport of native morphisms between changed successors. That needs compatible grade-map actions, not an equality of endpoints. The conditional split interface is not yet extracted from an arbitrary mathematical split fibration. See TELESCOPE_REINDEX_FREEZE.json and evidence/telescope-reindex-author-fresh.

Independent review passed for the bounded Type-valued reindexing result. See evidence/telescope-reindex-independent/Independent_Telescope_Reindex_Review.tex and the fresh build/audit logs there. Dependencies were cached. The general categorical and strict-algebra obligations remain open.

## One joint Grothendieck step after #171
Read eq:groth and the displayed native arrow, then GrothendieckStep.homEquiv, payload_comp, endpoint_square, restrict_payload and Endpoints.baseRestrict_arrow. Reconstruct the two opposites using the decoded payload arrow, not by guessing variance. Test the families-of-types witness on both Bool selectors. To compose restrictions for different base maps, supply coherence of the endpoint comparisons; Endpoints intentionally has no such fields. To extend to telescopes, use the obtained joint action, not the former same-successor product category. A fresh build may first need the pinned mathlib Grothendieck and Cat.Op modules; see the prerequisite build log.

Independent evidence: `evidence/grothendieck-step-independent/Review.tex`, fresh project build and 629 declaration audits.

For successive base arrows: read eq:groth, GrothendieckStep.restrict_payload, GrothendieckStep.restrictionCell_paste in GrothendieckCoherence.lean, then restrict_paste, Endpoints.Split and Endpoints.extensionPresheaf. The candidate freeze, telescope-172-baseline comparison, scoped author replay and acceptance note record verification. Reopen the split endpoint laws before transporting any conclusion to a general pseudofunctor or a weak cleavage.

Independent scoped pass: see `evidence/grothendieck-coherence-independent/Review.tex` and adjacent fresh project replay records (cached external dependencies).

For nondiscrete all-length transport, read manuscript eq:telescope on its right-hand side, then GrothendieckIterates.layer, Code/decode, successor_payload, packedPresheaf, summandDecode, and Witness.leaf_test. See GROTHENDIECK_ITERATES_FREEZE.json and evidence/grothendieck-iterates-author-fresh. The next comparison needs an independently constructed left-hand chain endpoint and hom interface, not a renaming of the iterate.

Independent scoped pass: see `evidence/grothendieck-iterates-independent/Review.tex` and the adjacent isolated project replay (664 indexed audits; cached external dependencies).

For the independent left-hand interface, read TelescopeSquares.Chain, next, Square, terminalMap, DecoratedHom before realizedEquiv, tailTarget, squareEquiv and verticalEquiv. Next independently paste squares, prove endpoint composition and compare induced payload composition to the native one. See TELESCOPE_SQUARES_FREEZE.json and evidence/telescope-squares-author-fresh.

Independent scoped pass: see `evidence/telescope-squares-independent/Review.tex` and adjacent fresh own-project replay (683 distinct audits; cached external dependencies). Independent chain-square identity and composition, and comparison preservation of both, remain open.

Resume after #175 via SquarePasting.headComp, next_comp, squareComp, terminal_comp and decoratedComp. Review compared_comp_head versus compared_zero_comp: full comparison preservation on transported tails, then category laws, remain to be proved. See SQUARE_PASTING_FREEZE.json and evidence/square-pasting-author-fresh.

Independent scoped pass: see `evidence/square-pasting-independent/Review.tex` and its fresh replay. At positive length the comparison of the pasted arrow has the specified head projection; this is not a comparison against an independently formed native composite. The double-successor witness tests the terminal map only.

After #176, inspect tail_paste (source), comparison_rebase (transport), compared_paste_tail (arbitrary-length tail), one_tail_native (general length-one payload component), and FamilyComparison.one_comp (full arrow, specialized model). Next obtain an inductive decomposition of nativePaste for general outer Grothendieck homs; matching only the independently compared tail is not yet that theorem. See TAIL_PASTING_FREEZE.json and evidence/tail-pasting-author-fresh.

Independent scoped pass: read `evidence/tail-pasting-independent/Review.tex` and the adjacent fresh replay before resuming the general native outer decomposition.

After #177, read Aligned and its same-hom equality lemma; then native_tail_decomposition together with compared_paste_tail from TailPasting, the induction square_comp_native, and decorated_assoc. The source operation was defined earlier in SquarePasting. Next compare the independent identities and derive unit laws before building a category-level equivalence. See NATIVE_SUCCESSOR_FREEZE.json and evidence/native-successor-author-fresh.

Independent scoped review passed: see `evidence/native-successor-independent/Review.tex` and the isolated 728-declaration replay (external dependency binaries cached). Identity preservation and source unit laws remain open.

After #178, read tail_identity and square_id_native, decorated_left_unit/right_unit, Fibre.paste and its comparison, Fibre.category, then Fibre.equivalence and Fibre.allEquivalence. Distinguish the fixed-base equivalences from as-yet unconstructed independent base restriction and its naturality. See CHAIN_IDENTITY_FREEZE.json and evidence/chain-identity-author-fresh.

Independent scoped pass: see `evidence/chain-identity-independent/Review.tex` and its fresh own-project replay (758 distinct named axiom audits; nine pinned external dependency caches reused). Source restriction and naturality in the base remain open.

After #179, inspect pullChain/endLift before realized_pull, then liftDecorated, compared_lift, Cartesian.unique_factor and Fibre.pullHom_square. The source arrow action has a cartesian specification. Compare Fibre.sourcePresheaf/allSourcePresheaf and allComparison_square with the previous allEquivalence. Next distinguish payload-change naturality and equipment-level sequential product identification from this base-only comparison. See CHAIN_RESTRICTION_FREEZE.json and evidence/chain-restriction-author-fresh.

Independent scoped pass: see `evidence/chain-restriction-independent/Review.tex` and the fresh 787-declaration replay (nine pinned external caches reused). The source arrow is the unique solution of the cartesian square; its proof uses comparison. Payload naturality and sequential span-product identification remain open.

For payload-variable eq:telescope inspect ChainPayload.base_square/layerMap and the independently defined onSquare before compared_square, mixed, sourceConstruction, iterateConstruction and allComparison_square. Next isolate the sequential-product comparison in the actual span equipment; higher modifications, universe closure and monad laws are distinct. See CHAIN_PAYLOAD_FREEZE.json and evidence/chain-payload-author-fresh.

Independent scoped pass: see `evidence/chain-payload-independent/Review.tex` and the fresh 822-declaration replay (nine pinned external caches reused). The forward maps commute with ordinary payload and base change; identification with sequential products of spans remains open.

For the span bridge, read SpanApex.right, Strict.commute/universal, strictFactor/strictEquivalence, then chainObjects/chainHoms/chainEndpoint_map. Next assemble an all-length functor: the span append extends the right end, while chain induction removes the left head. A decomposition at the last grade or a proved reassociation is required; a hom bijection alone proves no composition law.

Independent scoped pass: see `evidence/span-apex-independent/Review.tex` and the fresh 881-declaration replay (nine pinned dependency caches reused). Strict forward projections do not give a strict inverse over both legs; all-length pasting remains open.

For right-append assembly, start at Snoc.objects, Snoc.squares and terminal_append (no split needed). Compare chainHoms_id and chainHoms_comp for the complete binary arrows, then pointStep and powerPoints on the split span tower. The remaining inductive step must compare final grade arrows across the prefix endpoint transports on both sides and prove preservation of independently defined identities and pastings. Endpoint agreement or an object bijection alone does not supply that step.

Independent scoped pass: see evidence/chain-snoc-independent/Review.tex and the isolated 901-declaration replay (nine pinned external caches reused). Positive-power index zero is one primitive; all-length native arrow comparison remains open.

Read SpanArrows.gradeArrowCast, successorArrows and overArrow for endpoint-corrected reconstruction of a native arrow; last_paste and step_paste for independent versus native composition; powerEquivalence and comparison_source/dest for the positive-span conclusion. To connect the extension functors rather than their apices, carry an arbitrary payload presheaf along these actual comparison functors and check the induced map on its reindexed fibre arrows. Do not infer strict inverse leg preservation from the forward leg equalities. Revisit the pinned source at 458ff36a, lines 929–953 before treating the empty span, coproduct, or monad laws.

Independent scoped pass: see evidence/span-arrows-independent/Review.tex and the 936-declaration replay. Both forward leg equations are propositional functor equalities. Payload and nullary extensions remain open.

For the positive extension, read nativeEndpoint and weightedEquiv (strict vertical grade fibres), fibre_global and global_cartesian (the base-varying total), then pack/unpack and toIterate_natural (actual payload arrows and the pointwise iterate). Strict fibres need object-surjectivity of the comparison, not only essential surjectivity. For the remaining presheaf-level statement, identify a native cleavage over arbitrary base maps and compare its actions and coherence with inherited chain reindexing; a property of strongly cartesian arrows does not specify that cleavage. Return to 458ff36a, lines 929–953 before adjoining the empty span or invoking monoidality.

Independent scoped pass for the positive payload result: see `evidence/span-payload-independent/Review.tex` and its fresh 989-declaration replay. Next outstanding obligation: chosen native base reindexing and comparison with the iterate presheaf. Neither the strict fibre inclusion square nor cartesianness preservation supplies this datum.

For the native lift, follow pullObj/pullLift and cartesianLift, then extendChoice, powerChoice and payloadChoice. This route never calls an equivalence. For fibre arrows inspect Reindex.factor/map_fac and the strictly inverse repackaging FibreTotal.into/out. Route.compare_unique, compare_comp, compare_horizontal and associator_fac identify the coherence witnesses. Follow Evaluation.functor for arbitrary-base evaluation, native_cart for the universal property, then onFibre/fibreSquare and iterate_computation for the square's exact codomain. Before making a stronger claim, compare this fibre presentation to the original fixed-universe presheaf value on arrows, prove the mixed laws with #185's payload changes and the compatibility of constraints, and decide whether strict rather than invertible comparisons are required by the particular source conclusion.

Independent native-cleavage review completed. See evidence/native-cleavage-independent/Review.tex and its replay logs. Next: compare vertical arrows with the iterate presheaf action and exhibit base identity/composition laws of the evaluation squares, before mixed payload coherence.
