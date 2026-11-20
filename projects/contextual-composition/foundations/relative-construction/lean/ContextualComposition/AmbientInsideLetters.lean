module
public import ContextualComposition.AmbientLetterRead
public import ContextualComposition.AmbientDisjointFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInsideLetters
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates AmbientHorizontalDiagrams
open ContextadRoutes ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadInsideCells ContextadLawTransport
open ContextadOuterCharts ContextadCellWhisker SpanApex AmbientBlockCells AmbientModificationAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (k : Nat) {i j : Nat} {r s : Map S i j} (c : Cell r s)
theorem gradeFirst (x) :
    Pure ((blocks S k j).first.map ((insideCell k c).grade.hom.app x)) := by
  have h := (castIsoApp (normalize k r) (normalize k s).symm (core k c) x).map (blocks S k j).first
  apply alignPure h
  let t := (SuffixCell.alongIsoCell (power S k).dest (power S i).source (power S j).source r.over s.over c.grade (midVertical c)).hom.app ((blocks S k i).cutFunctor.obj x)
  change Pure (((blocks S k j).joinFunctor ⋙ (blocks S k j).first).map t)
  rw [(blocks S k j).join_first]; exact pureId _
theorem gradeRest (x) :
    Aligned ((blocks S k j).rest.map ((insideCell k c).grade.hom.app x))
      (c.grade.hom.app ((blocks S k i).rest.obj x)) := by
  apply ((castIsoApp (normalize k r) (normalize k s).symm (core k c) x).map (blocks S k j).rest).trans
  exact NativeCube.functorAlign (blocks S k j).join_rest _
theorem front (x) : Pure ((frontAt (S := S) (underlying X) k j).map ((rawCell X (insideCell k c)).hom.app x)) := by
  change Pure ((blocks S k j).first.map (gradeMap _))
  rw [readGrade]
  exact gradeFirst k c _
theorem totalMapPure {K J : Type*} [Category* K] [Category* J] {Y : Bᵒᵖ ⥤ Cat.{v,u}}
    (t : K ⥤ J) (e : J ⥤ B) {d : K ⥤ B} (h : t ⋙ e = d) {x y : Total Y d} (f : x ⟶ y) (p : Pure (payloadMap f)) :
    Pure (payloadMap ((SpanPayload.totalMap Y t e h).map f)) := by subst d; exact p
theorem tail (x) : Aligned ((tailAt (S := S) (underlying X) k j).map ((rawCell X (insideCell k c)).hom.app x))
    ((rawCell X c).hom.app ((tailAt (S := S) (underlying X) k i).obj x)) := by
  let a := (rawCell X (insideCell k c)).hom.app x
  let y := (tailAt (S := S) (underlying X) k i).obj x
  apply ContextadUnitTotal.pureAlign (underlying X) _
    (Functor.congr_obj (whiskTail (underlying X) k r) x) (Functor.congr_obj (whiskTail (underlying X) k s) x)
  · apply (NativeCube.functorAlign (SpanPayload.total_projection (underlying X) _ _ (blocks S k j).dest) a).trans
    change Aligned ((blocks S k j).rest.map (gradeMap a)) _
    rw [show gradeMap a = _ from WeightedCells.weightGrade _ _ _ _ (insideCell k c).endpoint x]
    apply (gradeRest k c _).trans
    apply (ContextadPayloadModification.appChange c.grade.hom (Functor.congr_obj (SpanPayload.total_projection (underlying X) _ _ (blocks S k i).dest).symm x)).trans
    exact (NativeCube.ofEq (WeightedCells.weightGrade _ _ _ _ c.endpoint y)).symm
  · exact totalMapPure _ _ _ a (readPure _ _ _)
  · exact readPure _ _ _
theorem alignParts {T K : Type u} [Category.{max u v} T] [Category.{max u v} K] (Y : Tᵒᵖ ⥤ Cat.{max u v,u}) (e : K ⥤ T) {x y x' y' : Total Y e}
    (A : x=x') (B : y=y') (f : x ⟶ y) (g : x' ⟶ y') (p : Pure (gradeMap f)) (q : Pure (gradeMap g))
    (h : Aligned ((ContextadWeakWeight.leafAt Y e).map f) ((ContextadWeakWeight.leafAt Y e).map g)) : Aligned f g := by
  subst x'; subst y'; exact NativeCube.ofEq (AmbientMateCalculus.foldEqual e (pureEq p q) h.eq)
section Read
open AmbientHorizontalRead AmbientHorizontalFrames ContextadWeakWeight
variable {a b : obj S i X ⟶ obj S j X} (t : a ⟶ b)
theorem readTotal (h : Reads t c) (y : Raw S X i) :
    Aligned ((totalCell t.hom.as).app ((chart S X i).obj y))
      ((chart S X j).map ((rawCell X c).hom.app y)) :=
  (NativeCube.functorAlign (chart S X j).asIsomorphism.counit_eq.symm ((totalCell t.hom.as).app ((chart S X i).obj y))).trans ((h y).map (chart S X j))
theorem framePoint (a : obj S i X ⟶ obj S j X) (p : Map S i j)
    (ha : tot a = global X p) (x) :
    (splitAt X k j).obj ((raw X (inside k p)).obj x) = (atEndpoint a.hom (power S k).dest).obj ((splitAt X k i).obj x) :=
  Functor.congr_obj ((splitInside X k p).trans (congrArg ((splitAt X k i) ⋙ ·) (ContextadUnitTotal.congrAction _ _ _ ha.symm))) x
theorem splitRead (h : Reads t c) (ha : tot a = global X r) (hb : tot b = global X s) (x) :
    Aligned ((splitAt X k j).map ((rawCell X (insideCell k c)).hom.app x))
      ((endpointCell (power S k).dest t.hom.as).app ((splitAt X k i).obj x)) := by
  let u := (rawCell X (insideCell k c)).hom.app x
  let y := (splitAt X k i).obj x
  let v := (endpointCell (power S k).dest t.hom.as).app y
  let H := splitAt (S := S) X k j
  have gp : Pure (gradeMap (H.map u)) :=
    AmbientMateCalculus.pureOfAligned (NativeCube.functorAlign (splitFront (underlying X) k j) u) (front X k c x)
  have ll : Aligned ((leafAt (underlying (obj S j X)) (power S k).dest).map (H.map u)) ((leafAt (underlying (obj S j X)) (power S k).dest).map v) := by
    apply (NativeCube.functorAlign (splitTail (underlying X) k j) u).trans
    apply ((tail X k c x).map (chart S X j)).trans
    apply (readTotal X c t h _).symm.trans
    apply (ContextadPayloadModification.appChange (totalCell t.hom.as) (Functor.congr_obj (splitTail (underlying X) k i).symm x)).trans
    exact (AmbientMateCalculus.endpointLeafAlign _ t.hom.as y).symm
  exact alignParts _ _ (framePoint X k a r ha x) (framePoint X k b s hb x) _ _ gp (endpointOver _ t.hom.as y) ll
end Read
end ContextualComposition.GrothendieckStep.AmbientInsideLetters
