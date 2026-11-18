import ContextualComposition.EndpointValues
import Mathlib.CategoryTheory.Category.Preorder

open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep
open NativePacked CutCompositor MovingCell ProjectedCharts EndpointValues
namespace IndependentRight
set_option backward.isDefEq.respectTransparency false
abbrev B := Nat
abbrev G : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of B)
def P : Endpoints.{0,0,0,0} B where
  grades := G
  extend _ := 𝟭 B
  lift _ := 𝟙 _
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := by apply heq_of_eq; apply Subsingleton.elim
inductive M where | star
instance : Category.{0} M where
  Hom _ _ := Nat
  id _ := 1
  comp f g := f * g
  id_comp := by intros; apply Nat.one_mul
  comp_id := by intros; apply Nat.mul_one
  assoc := by intros; apply Nat.mul_assoc
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of M)
noncomputable abbrev H : M ⥤ W S Y 0 :=
  (ZeroPower.eval Y 0).asEquivalence.inverse ⋙ Sigma.incl (C := coords S Y 0) (0,0) ⋙ (nativeEquiv S Y 0).functor
abbrev x := M.star
def z : x ⟶ x := (0 : Nat)
def e : x ⟶ x := 𝟙 x
theorem ze : z ≠ e := by change (0:Nat) ≠ 1; decide
theorem nz : ¬IsIso z := by
  intro h
  have c := IsIso.hom_inv_id z
  let k : Nat := inv z
  have hk : (0 : Nat) * k = (1 : Nat) := c
  simp at hk
noncomputable abbrev J := restrictValue S Y 0 (rightTotal S Y) (rightOver S Y)
example : (H ⋙ J).map z ≠ (H ⋙ J).map e := by
  unfold J; rw [EndpointValues.right]
  intro h
  apply ze
  apply (ZeroPower.eval Y 0).asEquivalence.inverse.map_injective
  apply (Sigma.incl (C := coords S Y 0) (0,0)).map_injective
  apply (nativeEquiv S Y 0).functor.map_injective
  exact (NativePacked.compare S Y 0).functor.map_injective h
example : ¬IsIso ((H ⋙ J).map z) := by
  unfold J; rw [EndpointValues.right]
  intro h
  let U := (ZeroPower.eval Y 0).asEquivalence.inverse
  let V := Sigma.incl (C := coords S Y 0) (0,0)
  let T := (nativeEquiv S Y 0).functor
  let R := (NativePacked.compare S Y 0).functor
  have : IsIso (R.map (T.map (V.map (U.map z)))) := h
  have := isIso_of_reflects_iso (T.map (V.map (U.map z))) R
  have := isIso_of_reflects_iso (V.map (U.map z)) T
  have := isIso_of_reflects_iso (U.map z) V
  exact nz (isIso_of_reflects_iso z U)
noncomputable abbrev K := restrictValue S Y 0 (leftTotal S Y) (leftOver S Y)
example : (H ⋙ K).map z ≠ (H ⋙ K).map e := by
  unfold K; rw [EndpointValues.left]
  intro h
  apply ze
  apply (ZeroPower.eval Y 0).asEquivalence.inverse.map_injective
  apply (Sigma.incl (C := coords S Y 0) (0,0)).map_injective
  apply (nativeEquiv S Y 0).functor.map_injective
  exact (BlockEvaluation.blockwise S Y 0).functor.map_injective h
example : ¬IsIso ((H ⋙ K).map z) := by
  unfold K; rw [EndpointValues.left]
  intro h
  let U := (ZeroPower.eval Y 0).asEquivalence.inverse
  let V := Sigma.incl (C := coords S Y 0) (0,0)
  let T := (nativeEquiv S Y 0).functor
  let R := (BlockEvaluation.blockwise S Y 0).functor
  have : IsIso (R.map (T.map (V.map (U.map z)))) := h
  have := isIso_of_reflects_iso (T.map (V.map (U.map z))) R
  have := isIso_of_reflects_iso (V.map (U.map z)) T
  have := isIso_of_reflects_iso (U.map z) V
  exact nz (isIso_of_reflects_iso z U)
end IndependentRight
