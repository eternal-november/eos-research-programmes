import ContextualComposition.NativePacked
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativePacked
namespace Unrestricted210
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B) (t : Y.obj (op A))
abbrev rows := NativeAssoc.Three.rows S
abbrev W := Lift.value Y A (rows S)
def row₀ : (rows S).source.Fiber A := ⟨⟨0,A⟩,rfl⟩
def row₁ : (rows S).source.Fiber A := ⟨⟨1,⟨0,A⟩⟩,rfl⟩
def w₀ : W S Y A := pair Y _ (row₀ S A) t
def w₁ : W S Y A := pair Y _ (row₁ S A) t
theorem incompatible (f : w₀ S Y A t ⟶ w₁ S Y A t) : False := by
  have g := (gradeMap f).val
  cases g
def emptyVal : Iterates.Packed P S Y (op A) := ⟨0,t⟩
abbrev D := Iterates.Packed P S ((PackedFree.free S).obj Y) (op A)
theorem sourceTag {x y : Iterates.Packed P S Y (op A)} (f : x ⟶ y) : x.1 = y.1 := by cases f; rfl
theorem obstruction (H : W S Y A ⥤ D S Y A)
    (i : (PackedCuts.mu S Y A).obj (H.obj (w₀ S Y A t)) ≅ emptyVal S Y A t)
    (j : (PackedCuts.mu S Y A).obj (H.obj (w₁ S Y A t)) ≅ emptyVal S Y A t) : ¬ H.Full := by
  intro hf; let _ := hf
  let x := H.obj (w₀ S Y A t); let y := H.obj (w₁ S Y A t)
  let μ := PackedCuts.mu S Y A
  obtain ⟨⟨v,g⟩,k⟩ := (PackedCuts.joinIncoming S Y A y).surjective ⟨μ.obj x,i.hom ≫ j.inv⟩
  have e : v = x := PackedCuts.zero_ext S Y A (congrArg Sigma.fst k) ((congrArg Sigma.fst (congrArg Sigma.fst k)).trans (sourceTag S Y A i.hom))
  exact incompatible S Y A t (H.preimage (eqToHom e.symm ≫ g))
end Unrestricted210
