module
public import ContextualComposition.NativeFubiniStructuralLaws
@[expose] public section

/-! Local interchange between the middle-four and swapping independent
factors. Symmetric, not merely braided, multiplication supplies it. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C]

def MedialSwap {T : Bi (coeff (C:=C))} {I : C} (P : TensorPrimitive T) (M : Middle T I) : Prop :=
  ∀ a b c d : C,
    M.cell a b c d ≫ T.map (P.swap a c) (P.swap b d) =
      P.swap (T.obj a b) (T.obj c d) ≫ M.cell c d a b

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem standardMedialSwap (mul : MonoidalCategory C) (symm : @SymmetricCategory C cat mul) :
    MedialSwap (@tensorPrimitives C cat mul symm.toBraidedCategory)
      (additiveMiddle (@Additive.ofBraided C cat mul symm.toBraidedCategory)) := by
  intro a b c d
  letI := mul
  letI := symm
  change tensorμ a b c d ≫ ((β_ a c).hom ⊗ₘ (β_ b d).hom) =
    (β_ (a ⊗ b) (c ⊗ d)).hom ≫ tensorμ c d a b
  simp only [tensorμ, braiding_tensor_left_hom, braiding_tensor_right_hom, tensorHom_def]
  monoidal
  calc
    _ = (c ◁ (α_ a d b).inv) ≫
          c ◁ (((β_ a d).hom ≫ (β_ d a).hom) ▷ b) ≫
          (c ◁ (α_ a d b).hom) ≫ (α_ c a (d ⊗ b)).inv := by
      rw [SymmetricCategory.symmetry]
      simp
    _ = _ := by
      rw [comp_whiskerRight, whiskerLeft_comp]
      simp only [Category.assoc]
      simp

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
