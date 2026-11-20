module
public import ContextualComposition.AmbientConstraintIsos
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientConstraintSquares
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open ContextadNativeLaws ContextadRoutes ContextadLawTransport ContextadModification AmbientSquareBridge
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
section Generic
variable {D : Type*} [Bicategory D] {X Y X' Y' : D} {u v : X ⟶ Y} {z : X' ⟶ Y'} {a a₀ : X ⟶ X'} {b b₀ : Y ⟶ Y'}
variable (p : u = v) (j : a = a₀) (k : b = b₀) (c : v ≫ b₀ ≅ a₀ ≫ z)
theorem twiceBent : bend p j k c = bend p rfl rfl (bend rfl j k c) := by subst v; subst a₀; subst b₀; simp [bend]
end Generic
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j : Nat} (p : Map S i j) (cp : gradeCart p) (a : ∀ Z : Obj.{u,v} B, obj S i Z ⟶ obj S j Z) (e : ∀ Z, a Z = oper S p cp Z)
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) {z : obj S i X ⟶ obj S i Y} (j₀ : z = AmbientBicategory.map S i f)
variable (s : z ≫ a Y ≅ a X ≫ AmbientBicategory.map S j f)
theorem original (h : s = bend j₀ (e X) (e Y) (comparison S p cp f)) :
    s = bend j₀ rfl rfl ((AmbientTypedConstraint.map p cp a e).naturality f) :=
  h.trans (twiceBent j₀ (e X) (e Y) (comparison S p cp f))
end ContextualComposition.GrothendieckStep.AmbientConstraintSquares
