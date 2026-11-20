module
public import ContextualComposition.ContentCovariantGrothendieck
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCovariantInput
open CategoryTheory CategoryTheory.Functor Opposite
open ContentCovariantGrothendieck
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B]

structure Endpoints (B : Type u) [Category.{u} B] where
  grades : B ⥤ Cat.{u,u}
  extend : ∀ A : B, grades.obj A ⥤ B
  lift : ∀ {A D : B} (v : A ⟶ D), extend A ⟶ (grades.map v).toFunctor ⋙ extend D

def asDual (L : Endpoints B) : GrothendieckStep.Endpoints.{u,u,u,u} Bᵒᵖ where
  grades := encode L.grades
  extend A := (L.extend A.unop).op
  lift v :=
    { app q := ((L.lift v.unop).app q.unop).op
      naturality _ _ k := congrArg Quiver.Hom.op ((L.lift v.unop).naturality k.unop).symm }

/-- Every strict covariant diagram is present in the decoded constructor;
there is no restriction to diagrams whose fibres are discrete. -/
def decodeEncode (Y : B ⥤ Cat.{u,u}) : decode (encode Y) ≅ Y :=
  isoWhiskerLeft Y Cat.opFunctorInvolutive ≪≫ Functor.rightUnitor Y

theorem extensionRead (L : Endpoints B) (A : B) :
    opOp (L.grades.obj A) ⋙ dest (asDual L) A = L.extend A := rfl

theorem cocartesianRead (L : Endpoints B) {A D : B} (v : A ⟶ D) (q : L.grades.obj A) :
    (ContentCovariantGrothendieck.lift (asDual L) v).app (op (op q)) = (L.lift v).app q := rfl

end ContextualComposition.GrothendieckStep.ContentCovariantInput
