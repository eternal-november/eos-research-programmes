module
public import ContextualComposition.AmbientInsideMate
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientInsideMateRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates ContextadRoutes
open ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadInsideCells ContextadLawTransport
open ContextadOuterCharts SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames ContextadWeakWeight AmbientInsideMate
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 550000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} {X Y : Obj.{u,v} B}
variable (f : X ⟶ Y) (k : Nat) {i j : Nat} (r : Map S i j) (p : gradeCart r)
theorem splitWeight (X : Obj.{u,v} B) : raw X (inside k r) ⋙ splitAt X k j =
    splitAt X k i ⋙ atEndpoint (oper S r p X).hom (power S k).dest :=
  (splitInside X k r).trans (congrArg (splitAt (S := S) X k i ⋙ ·) (ContextadUnitTotal.congrAction (power S k).dest _ _ (totalOper S X r p).symm))
theorem pairRoutes {A C D E F G : Type*} [Category* A] [Category* C] [Category* D] [Category* E] [Category* F] [Category* G]
    {r : A ⥤ C} {t : C ⥤ D} {u : A ⥤ E} {v : C ⥤ F} {w : D ⥤ G} {a : E ⥤ F} {b : F ⥤ G}
    (h : r ⋙ v = u ⋙ a) (q : t ⋙ w = v ⋙ b) : (r ⋙ t) ⋙ w = u ⋙ (a ⋙ b) :=
  (congrArg (r ⋙ ·) q).trans (congrArg (· ⋙ b) h)
theorem leftFrame : lRoute (power S (k+i)).dest (power S (k+j)).dest (inside k r).grade (inside k r).leg f.hom ⋙ splitAt Y k j =
    splitAt X k i ⋙ atEndpoint (oper S r p X ≫ AmbientBicategory.map S j f).hom (power S k).dest :=
  (pairRoutes (splitWeight k r p X) (splitAction f k j)).trans
    (congrArg (splitAt (S := S) X k i ⋙ ·) (atEndpointComp (oper S r p X).hom (AmbientBicategory.map S j f).hom (power S k).dest)).symm
theorem rightFrame : rRoute (power S (k+i)).dest (power S (k+j)).dest (inside k r).grade (inside k r).leg f.hom ⋙ splitAt Y k j =
    splitAt X k i ⋙ atEndpoint (AmbientBicategory.map S i f ≫ oper S r p Y).hom (power S k).dest :=
  (pairRoutes (splitAction f k i) (splitWeight k r p Y)).trans
    (congrArg (splitAt (S := S) X k i ⋙ ·) (atEndpointComp (AmbientBicategory.map S i f).hom (oper S r p Y).hom (power S k).dest)).symm
theorem read (x) :
    Aligned ((splitAt Y k j).map ((AmbientComparisonRead.q S (inside k r) f).app x))
      ((endpointCell (power S k).dest (comparison S r p f).inv.hom.as).app ((splitAt X k i).obj x)) := by
  let a := (AmbientComparisonRead.q S (inside k r) f).app x
  let y := (splitAt (S := S) (underlying X) k i).obj x
  let J := splitAt (S := S) (underlying Y) k j
  let t := (comparison S r p f).inv
  let b := (endpointCell (power S k).dest t.hom.as).app y
  have gr : Pure (gradeMap (J.map a)) := AmbientMateCalculus.pureOfAligned (NativeCube.functorAlign (splitFront (underlying Y) k j) a)
    (pureMap (blocks S k j).first (weakGrade _ _ _ _ f.hom x))
  have ll : Aligned ((leafAt (underlying (obj S j Y)) (power S k).dest).map (J.map a))
      ((leafAt (underlying (obj S j Y)) (power S k).dest).map b) := by
    apply (NativeCube.functorAlign (splitTail (underlying Y) k j) a).trans
    apply ((qTail f k r x).map (chart S Y j)).trans
    apply ((AmbientComparisonRead.comparisonAt S r p f ((tailAt (S := S) (underlying X) k i).obj x)).symm.map (chart S Y j)).trans
    apply (NativeCube.functorAlign (chart S Y j).asIsomorphism.counit_eq _).trans
    apply (ContextadPayloadModification.appChange (totalCell t.hom.as) (Functor.congr_obj (splitTail (underlying X) k i).symm x)).trans
    exact (AmbientMateCalculus.endpointLeafAlign _ t.hom.as y).symm
  exact AmbientInsideLetters.alignParts _ _ (Functor.congr_obj (leftFrame f k r p) x) (Functor.congr_obj (rightFrame f k r p) x)
    _ _ gr (endpointOver _ t.hom.as _) ll
end ContextualComposition.GrothendieckStep.AmbientInsideMateRead
