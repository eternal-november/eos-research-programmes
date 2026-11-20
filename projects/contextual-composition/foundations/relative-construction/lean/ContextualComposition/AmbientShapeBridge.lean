module
public import ContextualComposition.AmbientNamedSquare
public import ContextualComposition.AmbientSquareBridge
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientShapeBridge
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
section General
variable {C : Type*} [Bicategory C] {a b c d : C} {p q : a ⟶ b} {p' q' : c ⟶ d} {u : a ⟶ c} {v : b ⟶ d}
variable (r : u ≫ p' ≅ p ≫ v) (s : u ≫ q' ≅ q ≫ v)
variable (l L : p ≅ q) (k K : p' ≅ q')
open AmbientNamedSquare

variable (r' : u ≫ p' ≅ p ≫ v) (s' : u ≫ q' ≅ q ≫ v)
theorem changeEdges (h : r = r') (w : s = s') (k : Law r s L K) : Law r' s' L K := by subst r'; subst s'; exact k
theorem toSquare (h : Law r s L K) : Square r s L K := h
end General
end ContextualComposition.GrothendieckStep.AmbientShapeBridge
