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

For each input arrow u:a′→a at fixed output b, `mixedUnitInput` compares precomposing the pure label by u and then taking the mixed unit with taking the mixed unit and reindexing its H(a,b) value. At a label p:a→b the arrow is the tensor insertion of the first supplied unit’s naturality component and the identity on the second unit at 1b. These comparisons retain the endpoint and universe assumptions of the corresponding operations. The whole multiplication still requires an input square through the crossing and rebracketings, an output square, and coherent assembly of both endpoint actions.

## Reindexing the crossing and contraction stages

`Iterated.crossingInterchange` proves equality of strong transformations between changing the outer first factor and lifting a supplied middle crossing in either order. Applying the outer tensor gives `exposedCrossing_input`, equality of the two functors on the complete fourfold quotient in its middle-exposed bracketing. The supplied crossing may be noninvertible.

`mixedContractionInput` gives the natural isomorphism for the entire MM/NN contraction stage of mixed multiplication. It tensors the source-endpoint comparison of the actual M multiplication with the given N multiplication and uses the interchange law for the two tensor factors. The input comparison for the original multiplication must also transport these results across the two bracketing equivalences and the initial row identification.
