import ContextualComposition.RepresentableEndpointRealization
import ContextualComposition.RepresentableCompositionComparison
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open CategoryTheory.Bicategory RepresentableKleisli RepresentableNativeEndpoints
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace NonthinDirectedNative
set_option backward.isDefEq.respectTransparency false
inductive Token where | base
instance : Category.{0} Token where
  Hom _ _ := Nat
  id _ := 0
  comp a b := a + b
  id_comp := by intros; apply Nat.zero_add
  comp_id := by intros; apply Nat.add_zero
  assoc := by intros; apply Nat.add_assoc
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Token)
  extend A := (Functor.const Token).obj A
  lift u := { app := fun _ => u }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
def u : (0:Nat) ⟶ 1 := homOfLE (by decide)
def v : (0:Nat) ⟶ 2 := homOfLE (by decide)
def f : Arg (P := P) 0 0 := pair (RepresentableYoneda.rep 0) (P.extend 0) Token.base (Discrete.mk (𝟙 _))
def g : Arg (P := P) 1 2 :=
  pair (RepresentableYoneda.rep 2) (P.extend 1) Token.base (Discrete.mk (homOfLE (by decide : (1:Nat) ≤ 2)))
def dir (n : Nat) : Square u v f g :=
  ⟨show Token.base ⟶ Token.base from n, Subsingleton.elim _ _⟩
noncomputable def left := canonical (S := S) f
noncomputable def right := canonical (S := S) g
theorem leftRow : row left = f := RepresentableNativeComposition.canonicalEval (S := S) f
theorem rightRow : row right = g := RepresentableNativeComposition.canonicalEval (S := S) g
def move : Square u v f g ≃ Square u v (row left) (row right) := by rw [leftRow,rightRow]
noncomputable def original :=
  move.trans (RepresentableEndpointRealization.realization u v left right).symm
theorem bothOriginal : original (dir 0) ≠ original (dir 1) := by
  intro e
  have h := congrArg Subtype.val (original.injective e)
  exact Nat.zero_ne_one h
theorem exactRead (n : Nat) :
  move.symm (RepresentableEndpointRealization.realization u v left right (original (dir n))) = dir n :=
  original.symm_apply_apply _
theorem noInverseLeg : ¬ Nonempty ((1:Nat) ⟶ 0) := fun ⟨h⟩ => (by decide : ¬ (1:Nat) ≤ 0) (leOfHom h)
end NonthinDirectedNative
#print axioms NonthinDirectedNative.bothOriginal
#print axioms NonthinDirectedNative.exactRead
