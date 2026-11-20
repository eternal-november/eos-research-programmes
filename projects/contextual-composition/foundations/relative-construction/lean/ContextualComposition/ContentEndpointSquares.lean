module
public import ContextualComposition.ContentComma
public import ContextualComposition.RepresentableKleisliConstraints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentEndpointSquares
open CategoryTheory CategoryTheory.Functor Opposite
open ContentCovariantGrothendieck
open AmbientCoherentPseudomonad RepresentableKleisli
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ}
variable {A A' D D' : B}

abbrev OldRow (A D : B) := RepresentableComma.Row (P.extend (op D)) (op A)

def native (x : OldRow (P := P) A D) : ContentComma.Native P A D :=
  (ContentComma.read P A D).obj (op ((RepresentableComma.read (P.extend (op D)) (op A)).obj x))

/-- A native grade map is pushed along the output leg, not pulled along the input.
The body equation retains both directed endpoint arrows. -/
def Square (u : A ⟶ A') (v : D ⟶ D')
    (x : ContentComma.Native P A D) (y : ContentComma.Native P A' D') :=
  { beta : ((grades P).map v).toFunctor.obj x.right ⟶ y.right //
    x.hom ≫ (lift P v).app x.right ≫ (dest P D').map beta = u ≫ y.hom }

def compare (u : A ⟶ A') (v : D ⟶ D') (x : OldRow (P := P) A D) (y : OldRow (P := P) A' D') :
    RepresentableNativeEndpoints.Square v.op u.op y x ≃ Square u v (native x) (native y) where
  toFun t := ⟨t.val.op, by
    have h := congrArg Quiver.Hom.unop t.property
    change (RepresentableComma.body (P.extend (op D)) (op A) x).unop ≫
      ((P.lift v.op).app (grade _ _ x)).unop ≫ ((P.extend (op D')).map t.val).unop =
      u ≫ (RepresentableComma.body (P.extend (op D')) (op A') y).unop
    simpa only [unop_comp,Quiver.Hom.unop_op,Category.assoc] using h.symm⟩
  invFun t := ⟨t.val.unop, by
    have h := congrArg Quiver.Hom.op t.property
    change ((RepresentableComma.body (P.extend (op D)) (op A) x).unop ≫
      ((P.lift v.op).app (grade _ _ x)).unop ≫ ((P.extend (op D')).map t.val.unop).unop).op =
      (u ≫ (RepresentableComma.body (P.extend (op D')) (op A') y).unop).op at h
    simpa only [op_comp,Quiver.Hom.op_unop,← Category.assoc] using h.symm⟩
  left_inv t := Subtype.ext (by rfl)
  right_inv t := Subtype.ext (by rfl)

theorem sameGrade (u : A ⟶ A') (v : D ⟶ D') (x : OldRow (P := P) A D) (y : OldRow (P := P) A' D')
    (t : RepresentableNativeEndpoints.Square v.op u.op y x) :
    (compare u v x y t).val = t.val.op := rfl

variable {S : P.Split} (T : Data S)
noncomputable def bent (u : A ⟶ A') (v : D ⟶ D') (x : KH S (op D) (op A)) (y : KH S (op D') (op A')) :
    (compose T y (pureK T u.op) ⟶ compose T (pureK T v.op) x) ≃ Square u v (native (row x)) (native (row y)) :=
  (RepresentableKleisliConstraints.bent T v.op u.op y x).trans (compare u v (row x) (row y))

end ContextualComposition.GrothendieckStep.ContentEndpointSquares
