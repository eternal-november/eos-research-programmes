module
public import ContextualComposition.AmbientScheduleEdges
public import ContextualComposition.AmbientLeftFoldedRead
public import ContextualComposition.AmbientScheduleFragment
public import ContextualComposition.AmbientFourToTwo
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientIsoWords
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
open AmbientLetterRead
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
open AmbientNativeLetterFrame ContextadAppendCells
open AmbientScheduleFragment AmbientDeepIndices AmbientDisjointFrames
variable (X : Obj.{u,v} B) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
section Cat
variable {D : Type*} [Category D] {x y z t u w : D}
def Same (a b : x ≅ y) : Prop := a.hom = b.hom
theorem faces (a b l r : x ≅ y) (p : a = l) (q : b = r) (h : Same a b) : Same l r := by subst l; subst r; exact h
theorem sameHom (a b : x ≅ y) (h : Same a b) : a.hom = b.hom := h
theorem ofHom (a b : x ≅ y) (h : a.hom = b.hom) : Same a b := h
theorem triangle (a : x ≅ y) (b : y ≅ z) (c : x ≅ z) (j : z ≅ t) (h : a.hom ≫ b.hom = c.hom) :
    Same (a ≪≫ b ≪≫ j) (c ≪≫ j) := by unfold Same; simp only [Iso.trans_hom, ← Category.assoc, h]
theorem triBack (a : x ≅ y) (b : y ≅ z) (c : x ≅ z) (j : z ≅ t) (h : Same (a ≪≫ b ≪≫ j) (c ≪≫ j)) :
    a.hom ≫ b.hom = c.hom := by apply (cancel_mono j.hom).mp; simpa only [Same,Iso.trans_hom,Category.assoc] using h
theorem pentagon (a : x ≅ y) (b : y ≅ z) (c : z ≅ t) (d : x ≅ u) (j : u ≅ w) (e : w ≅ t)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ j.hom ≫ e.hom) : Same (a ≪≫ b ≪≫ c) (d ≪≫ j ≪≫ e) := h
theorem pentBack (a : x ≅ y) (b : y ≅ z) (c : z ≅ t) (d : x ≅ u) (j : u ≅ w) (e : w ≅ t)
    (h : Same (a ≪≫ b ≪≫ c) (d ≪≫ j ≪≫ e)) : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ j.hom ≫ e.hom := h
end Cat
end ContextualComposition.GrothendieckStep.AmbientIsoWords
