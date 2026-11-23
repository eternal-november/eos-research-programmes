# Relative tensors of weak Cat actions

This crosswalk follows the weak relative tensor theorem and the comma normalization lemma at manuscript revision `458ff36a`. Lean names are under `ContextualComposition`.

## Weak factors, universal property and representable units

The weak relative tensor theorem in the [relative-construction manuscript](../delivery/One_relative_construction_for_context_content_and_effects.tex) takes covariant and contravariant weak Cat actions over the same middle category. At fixed outer endpoints, `RelativeTensor.universalProperty` identifies functors and natural transformations out of the quotient with independently specified pseudobalanced cocones and their maps. The quotient retains native product-category arrows and inverts the designated middle balances subject to the weak compositor and unit laws. In the explicit collapsing action, `RelativeTensor.Collapse.product_noniso` and `inserted_iso` separate invertibility before and after insertion.

`RelativeTensor.LeftUnit.equivalence` and `RelativeTensor.RightUnit.equivalence` give the two representable unit comparisons at fixed outer endpoints. Their contractions compute on both native arrows and balances. `RelativeTensor.factor_order` identifies the two orders of changing strong factors on the whole quotient functor. `RelativeTensor.bifunctor` packages the joint action on strong factor transformations and their directed modifications. The declarations and their defining files are registered in the package theorem index.

## The actual tensor of the presented factors

For the comma normalization lemma in the [independent interaction criterion](../../../interaction/independent-criterion/General_Independent_Interaction_Criterion.tex), `RelativeTensor.Presented.equivalence` compares the actual generic quotient of the two presented factors with the normalized target at fixed endpoints. Its two comparison functors act on native arrows and on the invertible balances. The independently defined endpoint diagrams extend these comparisons to endpoint changes. The indexed result uses the generic weak tensor and the strong comparison squares of these presented factors.

`PseudonaturalInverse.equivalence` constructs an adjoint equivalence of Cat-valued pseudofunctors from a strong transformation whose component functors are equivalences. It preserves the original forward transformation. The unit, counit and triangle are constructed at the indexed level. Applying this result to the comparison gives `RelativeTensor.Presented.globalEquivalence` and its source-indexed form `sourceEquivalence`. The inverse uses mates of the pointwise equivalences. Arbitrary weak factors still require their own hypotheses to satisfy a comma normalization formula.

## Reassociation and four-factor scope

For a supplied weak curried middle action, `RelativeTensor.Iterated.associator` compares the full iterated quotient categories. The two functors are built from their actions on native arrows and inner and outer balance generators. `roundtrip_left` and `roundtrip_right` identify the composites with the identity functors. The transpose construction relates the two curried orientations. Interpreting an independently given uncurried middle pseudofunctor requires a comparison with these data.

`RelativeTensor.Iterated.twoStep` constructs one composite on the actual four-factor carriers. For the three-factor associator, `last_naturality` identifies the whole functors obtained by changing its last strong factor. The four-factor pentagon below identifies the two forward routes. The unitor–associator triangle below compares the two unit routes. Issue #93 also tracks generic mixed multiplication, pure pseudofunctor and companion-bending compatibility.

## Factor changes and the four-factor row comparison

For arbitrary strong maps of the first weak factor, `Iterated.first_naturality` identifies the two rebracketing functors on the entire localized category. `twoStep_first_naturality` proves the corresponding equality along the existing two-step route on four factors. For any directed modification of last-factor maps, `last_modification` identifies the whiskered natural transformations with the endpoint transports given by `last_naturality`.

`middleRow` identifies the row of the middle composite with the appropriate left inner action as a whole pseudofunctor, including its unit and compositor. `middleRow_change` compares the actual strong maps across that identification. The equivalence `rightRowAssociator` and the transport square `rightRow_change` apply this comparison at each source row. These comparisons enter the outer whiskerings of the three-step pentagon route.

## Whiskering rebracketing across a fourth factor

The `Iterated.outerAssociator` strong transformation varies the three-factor reassociation over the remaining covariant index. Its unit and composition diagrams carry the supplied weak structural cells through the actual component functors. `outerEquivalence` upgrades it to an indexed adjoint equivalence. Whiskering through the fourth factor gives `firstPentagonEquivalence : farLeft ≌ innerLeft`; `firstTwoEdges` then reaches `innerRight` using the associator of the actual middle composite.

On the other side, `OuterRow.naturality` gives the complete functor square at each opposite-index arrow. `first_modification` identifies the equation for every directed first-factor modification, and the row unit and compositor formulas record the actual structural components. `middleRow_insertion`, `middleRow_native` and `middleRow_balance` determine the row identification on native morphisms and the full outer balance isomorphism with its endpoint transports.

`twoStep_native` computes the existing two-step route on four simultaneous native arrows at fixed indices. The pentagon also requires a comparison on all three balance families and its extension to arbitrary quotient arrows.

## Generator criterion for the pentagon

For two functors out of `Iterated.farLeft` and a chosen isomorphism at every object, `fourGeneratorLaws_iff` characterizes naturality by its value on simultaneous native four-arrow tuples and the three specified forward junction balances. The extension to all quotient arrows uses the tensor universal property twice inside the outer quotient. It includes inverse balances. `isoOfFourGenerators` gives a natural isomorphism with exactly the supplied components. `extFourGenerators` yields functor equality when they are equality transports.

`OuterRow.direct` computes the right-row identification by an identity-on-fibres strong map; `direct_eq` compares it with the original row functor. The modules `RelativeTensorPentagonCoordinates`, `RelativeTensorFourBalanceB` and `RelativeTensorPentagonOuterBalance` compute the independent routes on each relevant native or balancing generator. The two complete outer-balance tests explicitly retain the object transports and their conditions on the last whiskering. In particular, the innermost balance uses its specified port. The proof below instantiates the last whiskering and all four comparisons.

## Weak compositor of the normalized outer row

For the actual contravariant first-index action on the middle composite, `OuterRow.columnUnit` and `OuterRow.columnComp` compute the native unit and compositor in each column. `OuterRow.normalize_unit` computes the image of the source unitor through the row identification for every vertex of the outer tensor.

`OuterRow.normalizedCompositor` computes the image of the source compositor through that identification for every composable pair and every vertex. Its equality records the source object, target object and morphism together. The underlying column calculation uses the actual weak compositor of the middle diagram. Pasting these equations with the row associator supplies the weak structure laws for the final right whiskering.

## The three-step route on four factors

`OuterRow.whisker` is the strong transformation between the two contravariant row diagrams. Its components are the concrete normalized row reassociations. The proof supplies both the weak unitor equation and the compositor equation for every composable pair of base arrows. Equality of the packed morphisms carries their two endpoints through the calculation.

`Iterated.rightPentagonRows` upgrades this transformation to an adjoint equivalence by its pointwise row equivalences. The resulting `Iterated.threeStep` is an equivalence from the fully left-bracketed relative tensor to the fully right-bracketed relative tensor, through both intermediate bracketings on the long route. `threeStep_functor` identifies the forward functor with that composite. `route_objects` gives the objectwise comparison with the two-step route for every strong last whiskering with the prescribed row functors.

## Four-factor pentagon

`RelativeTensor.Iterated.pentagon X M N Y` proves `(twoStep X M N Y).functor = (threeStep X M N Y).functor`. The equality holds on the whole fourfold quotient for arbitrary weak curried middle modules at the represented outer endpoints. Both sides come from independently constructed reassociation equivalences.

The simultaneous native-arrow comparison preserves all four payload arrows. Each of the three remaining generator comparisons uses the balance at its own junction. In particular, `whisker_port` supplies the object transport for the innermost balance, and `Pentagon.threeStep_middle` computes the central balance on primitive vertices. Every inner tensor object has a native vertex presentation. The four-generator criterion extends these computations to inverse balances and arbitrary quotient paths.

## Curried identity module and changes of the unit endpoint

For an ordinary middle category `B`, `Iterated.unitModule B` has fibre `Discrete (i ⟶ j)` at the pair `(i,j)`. Its columns are the Yoneda actions and its rows agree with the entire co-Yoneda actions, including the unit and compositor. `unitRowMap` identifies a row with its co-Yoneda presentation by identity functors on the label categories. `unitRowMap_tensor_change` proves that this identification commutes with a change of endpoint on the full quotient.

`LeftUnit.baseChange` and `RightUnit.baseChange` compare the fibre evaluation functors along precomposition and postcomposition, respectively. Their naturality applies to all tensor arrows. At a native vertex the comparison is the relevant compositor of the original weak factor. `RightUnit.indexedBase` specializes the right-hand square to the curried identity module.

## Indexed unit equivalences

`RightUnit.indexedEquivalence` evaluates the right unit on the actual diagram `leftInner X (unitModule B)`. Its base-change isomorphisms use the weak compositors of X, and satisfy the indexed unit and composition laws.

For the left unit, `LeftUnit.indexedEquivalence` first evaluates the co-Yoneda endpoint diagram. `unitRowEndpoint` identifies the actual curried row presentation with that diagram. Its fibre functor is induced by identity on each hom label, and its naturality components act by the identity on vertices. The resulting `Iterated.leftUnitEquivalence` has the actual left unitor as its forward strong transformation. On a row vertex, `leftUnitor_port` computes its base change by the compositor of Y. Its images of native arrows and balances are `leftUnitor_native` and `leftUnitor_balance`.

The local base-change formulas allow independent base and payload universes. Bundling each indexed equivalence into a single Cat-valued diagram uses a common universe large enough for the base objects, base morphisms and relevant payloads, as specified in the declaration.

## Unitor–associator triangle

`RelativeTensor.Iterated.UnitTriangle.triangle X Y` is the natural isomorphism from reassociating and applying the indexed left unitor to directly applying the indexed right unitor. Both are functors from the same threefold quotient to `Tensor X Y`. At the native vertex `[[x,p : i ⟶ j],y]`, the comparison is the original balance from `[i;x,Y(p)y]` to `[j;X(p)x,y]`, as computed by `UnitTriangle.triangle_app`.

Naturality on a simultaneous native arrow is the balanced cocone’s naturality equation. On each of the two junction balances, the comparison is its composition equation, with the weak compositor of X or Y in the orientation dictated by that junction. These three calculations extend to every quotient path, including inverse balances. The bundled routes use the common Cat levels of the indexed unitors. The separate mixed multiplication, realized bicategory, pure pseudofunctor and companion-bending statements of #93 have additional hypotheses and obligations.

## Endpoint formulas for the mixed unit and multiplication

The fixed-endpoint functors `Iterated.mixedUnitAt` and `Iterated.mixedMultiplicationAt` implement the arrows in `eq:unitMN` and `eq:multMN` of the [relative-construction manuscript](../delivery/One_relative_construction_for_context_content_and_effects.tex). Write H for `middleComposite M N`. At endpoints a,b the multiplication maps the actual fibre of H⊙H to the fibre of H. The inputs are strong module maps from N⊙M to M⊙N, from M⊙M to M, and from N⊙N to N. The crossing can be noninvertible.

`exposeMiddle` rebrackets the two paired tensors to expose N⊙M. `liftCrossing` applies the crossing under the left payload. `exposedCrossing_native` computes the result on an arbitrary arrow of the entire inner quotient together with both outer payload arrows. After rebracketing to the MM and NN pairs, the contractions come from `rowMultiplication` of the original M map and the column of the original N map. The row restriction retains the strong transformation’s original naturality isomorphisms.

For supplied units `jM,jN`, the right unitor’s inverse gives a section for splitting a pure arrow. `mixedUnitAt_obj` computes its value at p:a→b using the b-tagged pair `(jM(p),jN(𝟙 b))`. The unit is stated at the discrete hom module’s native Cat levels (v,v). The multiplication uses factor levels closed under the object and hom levels of the base and the fibres as displayed in its declaration. Both apply together, for example, for a small base and factors all in the same universe. Extending the unit to independently larger Cat levels requires explicit universe transport.

These endpoint formulas precede the global module transformations and their coherence. The mixed associativity and unit modifications, the laws deriving their pentagon and triangle from the supplied pseudodistributive law, and transport to the normalized comma presentation remain part of #93.

## Input-endpoint comparisons

For a strong map of curried modules, `Iterated.rowMap_changeIso` compares restricting to a row before and after reindexing the input endpoint. Its component at the output endpoint j is the original naturality isomorphism of the supplied component at j. `rowMultiplication_change` specializes this modification to the genuine M⊙M → M contraction used by `mixedMultiplicationAt`. Its source is the first-factor action on the actual left-inner tensor, identified with the reindexed row of M⊙M.

For each input arrow u:a′→a at fixed output b, `mixedUnitInput` compares precomposing the pure label by u and then taking the mixed unit with taking the mixed unit and reindexing its H(a,b) value. At a label p:a→b the arrow is the tensor insertion of the first supplied unit’s naturality component and the identity on the second unit at 1b. These comparisons retain the endpoint and universe assumptions of the corresponding operations. The input square for the whole multiplication is constructed below. The output square is also constructed below; coherent assembly of the endpoint actions is separate.

## Reindexing the crossing and contraction stages

`Iterated.crossingInterchange` proves equality of strong transformations between changing the outer first factor and lifting a supplied middle crossing in either order. Applying the outer tensor gives `exposedCrossing_input`, equality of the two functors on the complete fourfold quotient in its middle-exposed bracketing. The supplied crossing may be noninvertible.

`mixedContractionInput` gives the natural isomorphism for the entire MM/NN contraction stage of mixed multiplication. It tensors the source-endpoint comparison of the actual M multiplication with the given N multiplication and uses the interchange law for the two tensor factors. The comparison for the original multiplication also transports these results across the two bracketing equivalences and the initial row identification.

## Input-endpoint change for the original mixed multiplication

For the multiplication in `eq:multMN` of the [pinned source construction](https://github.com/eternal-november/eos-research-programmes/blob/458ff36a4798e432dee5947afc402f9903a47f14/projects/contextual-composition/foundations/relative-construction/delivery/One_relative_construction_for_context_content_and_effects.tex), [`Iterated.mixedMultiplicationInput`](ContextualComposition/RelativeTensorMixedMultiplicationInput.lean) is the natural isomorphism
`(H⊙H)(f,c) ⋙ μ(a,c) ≅ μ(b,c) ⋙ H(f,c)`, where `H=M⊙N`, `f:a→b`, and both `μ` are the original `mixedMultiplicationAt` functors. This compares functors on the full retained quotient, not just objects or native generators. It assumes the three supplied strong module maps (crossing and two contractions) and the same universe bounds as the multiplication. The crossing need not be invertible.

The column modification `outerAssociatorInput` comes from first-factor associator naturality. Tensoring it, and moving across the inverse associator by its unit and counit, gives `exposeMiddleInput`. The corresponding square and its mate enclose the exposed crossing to give `crossMiddleInput`. The original row-identification square and `mixedContractionInput` complete the comparison. Only the rebracketing equivalences are reversed. This is one input arrow at fixed output, not yet the identity/composition laws for those squares or mixed associativity.

## Output-endpoint change for the original mixed multiplication

For the same `eq:multMN`, [`Iterated.mixedMultiplicationOutput`](ContextualComposition/RelativeTensorMixedMultiplicationOutput.lean) supplies the natural isomorphism
`(H⊙H)(a,f) ⋙ μ(a,c) ≅ μ(a,b) ⋙ H(a,f)` for fixed input `a` and output change `f:b→c`. Its endpoints are the original functors on the full retained quotient, with the same assumptions as `mixedMultiplicationInput`.

The actual covariant transition of a composite column is its last-factor lift (`middleComposite_map_eq_lastMap`), and the initial row identification commutes with that change. Naturality of the associator in the last factor, its inverse mate, and binary factor interchange give the squares across the original crossing (`exposeMiddleOutput`, `crossMiddleOutput`). In `mixedContractionOutput` the cell is the original strong naturality of the N multiplication. The formula `contractChangeLast_app` inserts this cell next to the identity on the contracted M payload. Only the bracket equivalences are inverted, not the crossing or native arrows.

This constructs the output square for a single arrow. The output identity and composition laws are below. The input identity and composition laws, compatibility between directions, packaging as a strong map on the curried modules, and the mixed algebra laws remain separate.

## Identity law for the original mixed multiplication's output square

For `eq:multMN`, [`Iterated.mixedMultiplicationOutput_identity`](ContextualComposition/RelativeTensorMixedOutputIdentity.lean) proves the unit equation of the original output square at `f = 𝟙 b`. At every object of the fourfold retained carrier `(H⊙H)(a,b)`, the square followed by the actual output-action unitor of `H` equals the image under `mixedMultiplicationAt` of the actual output-action unitor of `H⊙H`. The two unitors are the covariant pseudofunctors' own `mapId` cells evaluated at the input fibre, not identities assumed for strict diagrams.

The relative tensor row identification, full crossing and its inverse rebracketings, and the contraction stage each satisfy the unit equation separately. The mate proof uses the equivalence triangle. The contraction unit equation is the supplied `N⊙N → N` map's own identity-naturality law, applied at the native second payload. This is endpoint-action coherence for the given multiplication, not a unit law for mixed multiplication itself.

## Composition law for the original mixed multiplication's output square

For `eq:multMN`, [`Iterated.mixedMultiplicationOutput_composition`](ContextualComposition/RelativeTensorMixedOutputComposition.lean) compares the original square at `f ≫ g` to the pasted squares at `f:b→c` and `g:c→d`, at fixed input `a`. On each object of the full retained `(H⊙H)(a,b)`, the direct square followed by the target action compositor agrees with the source action compositor mapped by `μ(a,d)`, followed by the `g` square and the `f` square whiskered by the target transition along `g`. The compositors are the two output actions' own `mapComp` cells, evaluated at `a` (`covariantCompAt`). No strictification or inverse of the crossing is used.

The proof pastes the row identification, the crossing with its actual rebracketing mates, and the contraction. The mate argument uses counit naturality and the equivalence triangle; the contraction uses the supplied `N⊙N → N` map's own `naturality_comp` on the native second payload. It has the same strong-map assumptions and universe bounds as the individual output square. A focused Lean build and a separate compiled-import axiom check cover this module. This is action coherence, not associativity of the mixed algebra.

## Identity law for the original mixed multiplication's input square

For `eq:multMN`, [`Iterated.mixedMultiplicationInput_identity`](ContextualComposition/RelativeTensorMixedInputIdentity.lean) proves the input identity-action equation at fixed output `b`. At every object of the retained `(H⊙H)(a,b)`, the original comparison at `𝟙 a` followed by the target action unitor agrees with the source action unitor mapped by `μ(a,b)`. Both unitors are the actual `mapId` cells in the contravariant columns, as evaluated by `contravariantUnitAt`. The input square’s original row identification and crossing orientation are unchanged.

Unlike the output proof, this compares the whole diagrams before and after the `middleRow` transport. `middleRow_changeUnit` matches the two unit cells including their dependent types. The contraction uses the supplied `M⊙M → M` map’s columnwise strong identity-naturality law, transported through that identification, and keeps the N payload fixed. The proof uses the same assumptions and universe bounds as the original square. This is input-action coherence, not a mixed algebra unit law. Input composition and compatibility of the two directions are separate.

## Composition law for the original mixed multiplication's input square

For `eq:multMN`, [`Iterated.mixedMultiplicationInput_composition`](ContextualComposition/RelativeTensorMixedInputComposition.lean) compares the original square at `f ≫ g` with the two successive input squares, at fixed output `d` and for `f:a→b`, `g:b→c`. Because the input action is contravariant, the source is `(H⊙H)(c,d)` and the transition along `g` comes before the one along `f`. The direct square followed by the target action compositor equals the image of the source action compositor under `μ(a,d)`, followed by the square at `f` and the square at `g` whiskered by `H(f,d)`. Both compositors are the original column `mapComp` cells (`contravariantCompAt`). The statement applies to all objects of the genuine retained quotient and compares natural transformations between original quotient functors.

`middleRow_changeComp` matches the compositor before and after the full row identification, including its dependent types. The proof pastes the original crossing, its rebracketing mates, and the contraction; the latter uses the given M multiplication's columnwise composition-naturality equation transported across those row identifications. No strictification or invertibility of the crossing is assumed. This is action coherence, not mixed associativity. Joint input-output compatibility and strong-map packaging remain separate.

## Do the original input and output changes agree when both endpoints move?

[`Iterated.mixedMultiplicationInputOutput_compatibility`](ContextualComposition/RelativeTensorMixedEndpointCompatibility.lean) proves the joint six-arrow law for the original mixed multiplication at two boundary arrows `f:a→b` and `g:c→d`. Starting at an object of the retained carrier `(H⊙H)(b,c)`, the two paths compare moving first contravariantly along `f` and then covariantly along `g`, versus moving in the opposite order. The outer faces are the actual strong-naturality interchangers of `(H⊙H).map g` and `H.map g` evaluated at `f.op` (`endpointInterchange`). The other four faces are the unchanged endpoint comparison isomorphisms. The result compares morphisms, not just the vertex functions.

The proof pastes the `rightRow_joint`, `crossMiddle_joint`, and `mixedContraction_joint` stages. The first checks whole-row identification; the second uses functor-level transport and the mates of the actual rebracketing equivalences, retaining their units and counits; the third compares the order of the two native contraction cells by product composition before insertion into the retained quotient. The crossing need not be invertible, and the proof does not require invertibility of native arrows. This is joint naturality, not mixed associativity or a mixed algebra unit law.

## The original mixed multiplication bundled as a strong map

For `eq:multMN`, [`Iterated.mixedMultiplication`](ContextualComposition/RelativeTensorMixedStrongMultiplication.lean) bundles the original multiplication into a strong transformation `H⊙H ⟶ H` of the weak curried modules. Its fibre functors are `mixedMultiplicationAt` (`mixedMultiplication_app`). At the named input and output port boundaries, the cells are the original `mixedMultiplicationInput` and `mixedMultiplicationOutput` (`namedColumnInput_eq`, `mixedColumnOutput_raw`, `rawOutput_eq`). The generic outer evaluation is `strongCurriedFromOrdinaryRawLaws_eval`. The source and target are the actual weak actions on the retained quotient.

Each fixed-output column is a strong map using the checked input laws. The already verified joint law is applied first to the four named multiplication ports, before these are projected from strong maps (`actualRawCube`). A generic transport then turns this into the exact bundled modification equation (`actualColumnCube`). The outer constructor consumes the original output unit and composition laws. No extra algebraic condition is imposed on the supplied strong crossing or contractions; in particular the crossing is not assumed invertible. This bundles endpoint coherence but does not establish mixed algebra unit or associativity.

## Output-endpoint change for the original mixed unit

For `eq:unitMN`, [`Iterated.mixedUnitOutput`](ContextualComposition/RelativeTensorMixedUnitOutput.lean) compares postcomposing a pure label by `g:b→c` and then taking the mixed unit with taking the unit and applying the actual output transition of `H=M⊙N`, at fixed input `a`. At `p:a→b`, `mixedUnitOutput_app` starts with the original c-tagged unit pair at `p≫g`. It applies the first unit's output naturality, takes the inverse middle balance, then applies the second unit's inverse input naturality at `𝟙 c` and forward output naturality at `𝟙 b`. The only intervening label cast is `g≫𝟙 c = 𝟙 b≫g`. The inverse balance is one of the designated isomorphisms of the retained quotient, not an inversion of a native arrow.

The comparison uses the original `mixedUnitAt` and both supplied strong native units, with the same universe bounds as the input square. This is the output square for one arrow. Identity/composition coherence for the input and output comparisons, their joint compatibility, and bundling the unit into a global strong transformation remain separate, as do mixed multiplication's algebra unit laws.

## Covariant coherence of the original mixed unit

For `eq:unitMN`, [`Iterated.mixedUnitOutput_identity` and `Iterated.mixedUnitOutput_composition`](ContextualComposition/RelativeTensorMixedUnitOutputCoherence.lean) prove the weak identity and composition equations of the existing `mixedUnitOutput`. They use the chosen unitors and compositors of the actual actions, without strictifying the original tensor quotient. The identity proof uses the identity balance relation and the input and output identity laws of the supplied native units. For composition, faithful contraction to the discrete hom fibre identifies the literal splitting square with the chosen-equivalence mate. This mate and the two strong factor stages supply the compositor law; the proof identifies the pasted square with the original `mixedUnitOutput` by expanding the images of the inverse balance.

At common native Cat levels, `mixedUnitOutputRow` bundles this as a strong map with the input fixed. Its components and naturality are `mixedUnitAt` and `mixedUnitOutput` (`mixedUnitOutputRow_app` retains the dependent fibre type via heterogeneous equality; `mixedUnitOutputRow_naturality` is ordinary equality). The row bundling writes the base hom level as `max u v` when the object level is `u`; the two pointwise coherence theorems retain the original general object and hom levels. Input coherence and compatibility between the directions, and hence a curried global strong map for the unit, remain separate. None of these results is an algebra unit law for the mixed multiplication.

## Contravariant coherence of the original mixed unit

For `eq:unitMN`, [`Iterated.mixedUnitInput_identity` and `Iterated.mixedUnitInput_composition`](ContextualComposition/RelativeTensorMixedUnitInputCoherence.lean) prove the original input comparison's weak unit and composition equations at fixed output. The compositors are the actual column `mapComp` cells, with the transition along `g` before that along `f` for (f:a→b) and (g:b→c). At the native vertex, they act on the first payload and keep the second supplied unit at the identity label fixed. Inserting the chosen strong naturality equations of the first native unit gives the equations on the original quotient. No balance or native arrow is inverted in this proof.

At common native Cat levels, `mixedUnitInputColumn` bundles this as a strong map with output fixed. Its component functors are the original `mixedUnitAt` (heterogeneous equality retaining the dependent fibre type), and its naturality is ordinarily equal to the original `mixedUnitInput`. The column bundling writes the base hom level as `max u v` when the object level is `u`; the two equation theorems retain the original general object and hom levels. Separate input and output coherence do not imply joint compatibility or a global curried strong map. This is not an algebra unit law.
