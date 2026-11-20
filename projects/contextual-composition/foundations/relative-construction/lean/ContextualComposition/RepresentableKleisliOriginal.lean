module
public import ContextualComposition.RepresentableAssociatorMiddle
public import ContextualComposition.RepresentablePentagonCorner
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliOriginal
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli RepresentableKleisliConstraints RepresentableKleisliGeneric
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
noncomputable abbrev F : StrictPseudofunctor (Obj.{u,u} B) (Obj.{u,u} B) := action S 1
noncomputable def μ (X : Obj.{u,u} B) : (F (S := S)).obj ((F (S := S)).obj X) ⟶ (F (S := S)).obj X :=
  M S X T.mult
noncomputable def D {X Y : Obj.{u,u} B} (f : X ⟶ Y) : (F (S := S)).map ((F (S := S)).map f) ≫ μ T Y ≅ μ T X ≫ (F (S := S)).map f :=
  squareM S T.mult f
noncomputable def a (X : Obj.{u,u} B) : μ T ((F (S := S)).obj X) ≫ μ T X ≅ (F (S := S)).map (μ T X) ≫ μ T X :=
  assocIso T X
variable {V W X Y : B}
theorem cmpPin (f : KH S V W) (g : KH S W X) :
    cmp (F (S := S)) (μ T) f g = compose T f g := rfl
theorem cellPin {f f' : KH S V W} {g g' : KH S W X} (t : f ⟶ f') (k : g ⟶ g') :
    RepresentableKleisliGeneric.cell (F (S := S)) (μ T) t k = composeCell T t k := rfl
theorem bendPin (f : KH S V W) (g : KH S W X) (h : KH S X Y) :
    bend (F (S := S)) (μ T) (D T) (a T) f g h = reassociate T f g h := by
  rw [shape]
  rfl
set_option linter.defProp false in
def middleRaw (f : KH S V W) {g g' : KH S W X} (t : g ⟶ g') (h : KH S X Y) :=
  RepresentableAssociatorMiddle.exactMiddle (V := yObj V) (W := yObj W) (X := yObj X) (Y := yObj Y)
    (F (S := S)) (μ T) (D T) (a T) f t h
theorem middle (f : KH S V W) {g g' : KH S W X} (t : g ⟶ g') (h : KH S X Y) :
    composeCell T (composeCell T (𝟙 f) t) (𝟙 h) ≫ (reassociate T f g' h).hom =
    (reassociate T f g h).hom ≫ composeCell T (𝟙 f) (composeCell T t (𝟙 h)) := by
  have H := middleRaw T f t h
  rw [bendPin,bendPin,cellPin,cellPin,cellPin,cellPin] at H
  exact H
end ContextualComposition.GrothendieckStep.RepresentableKleisliOriginal
