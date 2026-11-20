module
public import ContextualComposition.AmbientSquareBridge
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNamedSquare
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
def Law : Prop := Square r s L K
theorem move (h : l = L) (w : k = K) (z : Square r s l k) : Law r s L K := by subst L; subst K; exact z
end General
variable {i j : Nat} {p q : Map S i j} (c : Cell p q) (pc : gradeCart p) (qc : gradeCart q)
variable {a : obj S i X ⟶ obj S i Y} (e : a = AmbientBicategory.map S i f)
variable {u v : obj S i X ⟶ obj S j X} {u' v' : obj S i Y ⟶ obj S j Y}
variable (h : u = oper S p pc X) (h' : u' = oper S p pc Y) (z : v = oper S q qc X) (z' : v' = oper S q qc Y)
variable (l : a ≫ u' ≅ u ≫ AmbientBicategory.map S j f) (t : a ≫ v' ≅ v ≫ AmbientBicategory.map S j f)
variable (w : l = bend e h h' (comparison S p pc f)) (w' : t = bend e z z' (comparison S q qc f))
variable (L : u ≅ v) (R : u' ≅ v')
include w w' in
theorem close (a : reframe h z (AmbientNativeModification.cmp c pc qc X) = L) (b : reframe h' z' (AmbientNativeModification.cmp c pc qc Y) = R) :
    Law l t L R := move l t _ L _ R a b (viaNative c pc qc f e h h' z z' l t w w')
end ContextualComposition.GrothendieckStep.AmbientNamedSquare
