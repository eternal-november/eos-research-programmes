import ContextualComposition.RepresentableEndpointRealization
import ContextualComposition.RepresentableCompositionComparison
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open CategoryTheory.Bicategory RepresentableKleisli RepresentableNativeEndpoints
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace DirectedNativeEndpoints
set_option backward.isDefEq.respectTransparency false
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend A := (Functor.const Nat).obj A
  lift u := { app := fun _ => u }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
def u : (0:Nat) ⟶ 1 := homOfLE (by decide)
def v : (0:Nat) ⟶ 2 := homOfLE (by decide)
def f : Arg (P := P) 0 0 := pair (RepresentableYoneda.rep 0) (P.extend 0) (0:Nat) (Discrete.mk (𝟙 _))
def g : Arg (P := P) 1 2 := pair (RepresentableYoneda.rep 2) (P.extend 1) (1:Nat) (Discrete.mk (homOfLE (by decide : (1:Nat) ≤ 2)))
def direct : Square u v f g := ⟨(show (0:Nat) ⟶ 1 from homOfLE (by decide)),Subsingleton.elim _ _⟩
theorem noInverseLeg : ¬ Nonempty ((1:Nat) ⟶ 0) := fun ⟨h⟩ => (by decide : ¬ (1:Nat) ≤ 0) (leOfHom h)
theorem forwardGrade : gradeMap ((edgeEquiv u v f g).symm direct) = direct.val := rfl
noncomputable def left := canonical (S := S) f
noncomputable def right := canonical (S := S) g
theorem leftRow : row left = f := RepresentableNativeComposition.canonicalEval (S := S) f
theorem rightRow : row right = g := RepresentableNativeComposition.canonicalEval (S := S) g
noncomputable def squareAt : Square u v (row left) (row right) := by rw [leftRow,rightRow]; exact direct
noncomputable def observed := (RepresentableEndpointRealization.realization u v left right).symm squareAt
theorem survives : (RepresentableEndpointRealization.realization u v left right) observed = squareAt :=
  (RepresentableEndpointRealization.realization u v left right).apply_symm_apply squareAt
end DirectedNativeEndpoints
#print axioms DirectedNativeEndpoints.survives
