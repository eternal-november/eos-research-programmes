module
public import ContextualComposition.AmbientSquareBridge
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientRebasedStrong
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientSquareBridge AmbientHorizontalNaturality
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {D E : Type*} [Bicategory D] [Bicategory E] {F G : Pseudofunctor D E}
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
variable (t : StrongTrans F G) (a : ∀ Z, F.obj Z ⟶ G.obj Z) (e : ∀ Z, a Z = t.app Z)
def spoke {X Y : D} (f : X ⟶ Y) : F.map f ≫ a Y ≅ a X ≫ G.map f := bend rfl (e X) (e Y) (t.naturality f)
theorem idSpoke {X Y : D} (f : X ⟶ Y) : spoke t t.app (fun _ => rfl) f = t.naturality f := by simp [spoke,bend]
def strong : StrongTrans F G where
  app := a
  naturality := spoke t a e
  naturality_naturality {X Y} {f g} v := by
    cases (funext e : a = t.app).symm
    simpa only [idSpoke] using t.naturality_naturality v
  naturality_id X := by
    cases (funext e : a = t.app).symm
    simpa only [idSpoke] using t.naturality_id X
  naturality_comp {X Y Z} f g := by
    cases (funext e : a = t.app).symm
    simpa only [idSpoke] using t.naturality_comp f g
variable (s : StrongTrans F G) (b : ∀ Z, F.obj Z ⟶ G.obj Z) (w : ∀ Z, b Z = s.app Z)
variable (m : ∀ Z, t.app Z ≅ s.app Z) (n : ∀ {X Y} (f : X ⟶ Y), Square (t.naturality f) (s.naturality f) (m X) (m Y))
def modification : strong t a e ≅ strong s b w :=
  StrongTrans.isoMk (η := strong t a e) (θ := strong s b w) (fun Z => reframe (e Z) (w Z) (m Z)) fun {X Y} f =>
    AmbientSquareBridge.transport rfl (e X) (e Y) (w X) (w Y) (t.naturality f) (s.naturality f) (m X) (m Y) (n f)
end ContextualComposition.GrothendieckStep.AmbientRebasedStrong
