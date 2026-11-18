import ContextualComposition.PackedCuts
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep PackedCuts
namespace Orders210
-- Primitive labels are discrete but context-dependent payloads distinguish every decimal step of the cut.
def extF (a : Nat) : Discrete Nat ⥤ Nat := Discrete.functor (fun k : Nat => 10*a+k)
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of (Discrete Nat))
  extend := extF
  lift {a a'} f := { app := fun k => homOfLE (Nat.add_le_add_right (Nat.mul_le_mul_left 10 f.le) k.as) }
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj n := Cat.of (Fin n.unop → Nat)
  map f := (Pi.comap (fun _ => Nat) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def V : Fin 1468 → Nat := fun i => i.val+5
abbrev G (k : Nat) := Discrete.mk k
def l₁ : (PackedFree.pow S Y 1).obj (op 146) := pair _ _ (G 8) V
def l₂ : (PackedFree.pow S Y 2).obj (op 14) := pair _ _ (G 6) l₁
def path : (PackedFree.pow S Y 3).obj (op 1) := pair _ _ (G 4) l₂
abbrev out := Iterates.Packed P S Y (op 1)
def x : out := ⟨3,path⟩
abbrev double := Iterates.Packed P S ((PackedFree.free S).obj Y) (op 1)
def cut₀ : double := ⟨0,x⟩
def cut₁ : double := ⟨1,pair _ _ (G 4) (show Iterates.Packed P S Y (op 14) from ⟨2,l₂⟩)⟩
def cut₂ : double := ⟨2,pair _ _ (G 4) (pair _ _ (G 6) (show Iterates.Packed P S Y (op 146) from ⟨1,l₁⟩))⟩
def cut₃ : double := ⟨3,pair _ _ (G 4) (pair _ _ (G 6) (pair _ _ (G 8) (show Iterates.Packed P S Y (op 1468) from ⟨0,V⟩)))⟩
example : (cutEquiv S Y 1).functor.obj ⟨(0,3),path⟩ = cut₀ := rfl
example : (cutEquiv S Y 1).functor.obj ⟨(1,2),path⟩ = cut₁ := rfl
example : (cutEquiv S Y 1).functor.obj ⟨(2,1),path⟩ = cut₂ := rfl
example : (cutEquiv S Y 1).functor.obj ⟨(3,0),path⟩ = cut₃ := rfl
example : (mu S Y 1).obj cut₁ = x := Functor.congr_obj (cut_join_at S Y 1 (1,2)) path
example : (mu S Y 1).obj cut₃ = x := Functor.congr_obj (cut_join_at S Y 1 (3,0)) path
end Orders210
