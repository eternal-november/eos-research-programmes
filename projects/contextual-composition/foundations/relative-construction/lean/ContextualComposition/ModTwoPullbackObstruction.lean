module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-! Tensoring the pullback of multiplication by two along zero with ℤ/2. The global pullback has a nonzero first projection, while the local tensor maps every point to zero. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.ModTwoPullbackObstruction

open scoped TensorProduct

variable {X Y M : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup M]

/-- The kernel carries the linear pullback of f along the zero-object leg; the leg to zero is unique. -/
theorem kernel_factor (f : X →ₗ[ℤ] Y) (a : M →ₗ[ℤ] X) (e : f.comp a = 0) :
    ∃! r : M →ₗ[ℤ] LinearMap.ker f, (LinearMap.ker f).subtype.comp r = a := by
  let r := a.codRestrict (LinearMap.ker f) (fun x => LinearMap.congr_fun e x)
  refine ⟨r,rfl,?_⟩
  intro z hz; apply LinearMap.ext; intro x
  exact Subtype.ext (LinearMap.congr_fun hz x)

def double : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id

theorem local_zero (x : LinearMap.ker double) : x.val=0 := by
  have h : 2*x.val = 0 := x.property
  omega

abbrev Bit := ZMod 2
abbrev Local := LinearMap.ker double ⊗[ℤ] Bit
abbrev Global := LinearMap.ker (double.rTensor Bit)
def first : Local →ₗ[ℤ] ℤ ⊗[ℤ] Bit := (LinearMap.ker double).subtype.rTensor Bit

theorem first_zero (p : Local) : first p = 0 := by
  induction p using TensorProduct.inductionOn with
  | tmul x y =>
    change (LinearMap.ker double).subtype.rTensor Bit (x ⊗ₜ y) = _
    rw [LinearMap.rTensor_tmul]; change (x.val ⊗ₜ[ℤ] y) = 0
    rw [local_zero x,TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add,hx,hy,add_zero]

theorem transformed_zero (p : ℤ ⊗[ℤ] Bit) : double.rTensor Bit p = 0 := by
  induction p using TensorProduct.inductionOn with
  | tmul x y =>
    rw [LinearMap.rTensor_tmul]
    apply (TensorProduct.lid ℤ Bit).injective
    rw [TensorProduct.lid_tmul,map_zero]
    change (2*x) • y = 0
    rw [mul_smul]
    change (2 : ℤ) • (x • y) = 0
    simp [zsmul_eq_mul]
    rw [show (2 : Bit) = 0 by decide, zero_mul]
  | add x y hx hy => rw [map_add,hx,hy,add_zero]

def forward : Local →ₗ[ℤ] Global := first.codRestrict _ (fun _ => transformed_zero _)

def nonzero : Global := ⟨1 ⊗ₜ[ℤ] (1:Bit),transformed_zero _⟩
theorem separates : nonzero.val ≠ 0 := by
  intro eq
  have e := congrArg (TensorProduct.lid ℤ Bit) eq
  change (TensorProduct.lid ℤ Bit) (1 ⊗ₜ[ℤ] (1:Bit)) = _ at e
  rw [TensorProduct.lid_tmul,one_smul,map_zero] at e
  exact one_ne_zero e

/-- Even a set map reversing the comparison cannot preserve the first cone leg. -/
theorem no_reverse : ¬ ∃ r : Global → Local, ∀ x, first (r x) = x.val := by
  rintro ⟨r,h⟩; exact separates ((h nonzero).symm.trans (first_zero _))

end ContextualComposition.ModTwoPullbackObstruction
