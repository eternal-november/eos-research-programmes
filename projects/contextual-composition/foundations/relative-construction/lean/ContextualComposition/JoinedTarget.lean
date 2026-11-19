module
public import ContextualComposition.JoinedBinary
public import ContextualComposition.WhiskerSquares
@[expose] public section
namespace ContextualComposition.GrothendieckStep.JoinedTarget
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativePacked MovingCoordinates MovingCell ProjectedCharts TaggedTripleFaces WholeEvaluator
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
noncomputable def joinedPrefix := isoWhiskerLeft (dropLast S Y) (JoinedBinary.joined S (one S Y))
noncomputable def joinedSuffix := isoWhiskerLeft (regrouping S Y) (isoWhiskerRight
  (SuffixCell.foldIsoCell Y (ChartRealization.twice S Y) (U S).dest (pairSpan S).source (pairSpan S).dest
    (rightOver S Y) (binaryOver S Y) (JoinedBinary.joined S Y) (JoinedBinary.vertical S Y)) (outer S Y))
noncomputable def comparison := joinedPrefix S Y ≪≫ eqToIso (ordinary S Y) ≪≫ (joinedSuffix S Y).symm
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem before (I : C ⥤ D) {F G H : D ⥤ E} (a : F ≅ G) (b : G ≅ H) (c : F ≅ H) (e : a.hom ≫ b.hom = c.hom) :
    (isoWhiskerLeft I a).hom ≫ (isoWhiskerLeft I b).hom = (isoWhiskerLeft I c).hom := congrArg (whiskerLeft I) e
end General
section Prefix
set_option backward.isDefEq.respectTransparency true
theorem liftedPrefix : (isoWhiskerLeft (dropLast.{u,v} S Y) (cell.{u,v} S (one.{u,v} S Y))).hom ≫
    (isoWhiskerLeft (dropLast.{u,v} S Y) (JoinedBinary.joined.{u,v} S (one.{u,v} S Y))).hom =
    (isoWhiskerLeft (dropLast.{u,v} S Y) (CutReadout.bridge.{u,v} S (one.{u,v} S Y))).hom :=
  before (dropLast.{u,v} S Y) (cell.{u,v} S (one.{u,v} S Y)) (JoinedBinary.joined.{u,v} S (one.{u,v} S Y))
    (CutReadout.bridge.{u,v} S (one.{u,v} S Y)) (JoinedBinary.compatible.{u,v} S (one.{u,v} S Y))
theorem prefixLaw : (first.{u,v} S Y).hom ≫ (joinedPrefix.{u,v} S Y).hom = (prefixToStages.{u,v} S Y).hom := by
  unfold first joinedPrefix prefixToStages
  exact liftedPrefix.{u,v} S Y
end Prefix
theorem suffixLaw : (last S Y).hom ≫ (joinedSuffix S Y).hom = (suffixToStages S Y).hom :=
  WhiskerSquares.whiskComposite (regrouping S Y) (outer S Y) _ _ _ (WhiskerSquares.foldComposite Y (ChartRealization.twice S Y) (U S).dest (pairSpan S).source (pairSpan S).dest
    (leftOver S Y) (rightOver S Y) (binaryOver S Y) (cell S Y) (JoinedBinary.joined S Y) (CutReadout.bridge S Y)
    (FibreEndpoints.totalVertical S Y) (JoinedBinary.vertical S Y) (bridgeVertical S Y (CutReadout.readout S Y)) (JoinedBinary.compatible S Y))
theorem square : (first S Y).hom ≫ (comparison S Y).hom = (sourceCorner S Y).hom ≫ (last S Y).hom :=
  WhiskerSquares.twoFaces (first S Y).hom (last S Y).hom (prefixToStages S Y) (joinedPrefix S Y) (suffixToStages S Y) (joinedSuffix S Y)
    (eqToIso (ordinary S Y)) (prefixLaw S Y) (suffixLaw S Y)
end ContextualComposition.GrothendieckStep.JoinedTarget
