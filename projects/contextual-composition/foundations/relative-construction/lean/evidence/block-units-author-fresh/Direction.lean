import ContextualComposition.BlockUnits
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedCuts
namespace Directional213
set_option backward.isDefEq.respectTransparency false
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
open BlockUnits CutCompositor NativePacked NativeBlocks
-- Actual η at TY places no grades outside; Tη places all three outside.
example : (insert S Y 1 .left).obj x = cut₀ := rfl
example : (insert S Y 1 .right).obj x = cut₃ := rfl
example : IsEmpty (cut₀ ⟶ cut₃) := ⟨fun f => (by decide : (3 : Nat) ≠ 0) (wrongSide S Y 1 (x := x) f)⟩
-- An interior cut is not either unit even though all three have exactly the same product.
example : IsEmpty (cut₁ ⟶ cut₀) ∧ IsEmpty (cut₁ ⟶ cut₃) := by
  have t : profile S Y 1 cut₁ = (1,2) := profile_at S Y 1 (1,2) path
  constructor
  · exact ⟨fun f => (by decide : (1 : Nat) ≠ 0) (congrArg Prod.fst (t.symm.trans ((profile_map S Y 1 f).trans (insertShape S Y 1 .left x))))⟩
  · exact ⟨fun f => (by decide : (1 : Nat) ≠ 3) (congrArg Prod.fst (t.symm.trans ((profile_map S Y 1 f).trans (insertShape S Y 1 .right x))))⟩
abbrev z : (power S 3).apex := pair P.grades _ (pair P.grades _ (pair P.grades (𝟭 Nat) 1 (G 4)) (G 6)) (G 8)
def p : BlockUnits.single S Y 1 := pair Y _ ⟨⟨3,z⟩,rfl⟩ V
def q : BlockUnits.single S Y 1 := pair Y _ ⟨⟨3,z⟩,rfl⟩ (fun i => V i + 1)
def up : p ⟶ q := arrow (𝟙 _) (fun _ => homOfLE (Nat.le_succ _))
theorem noniso : ¬ IsIso up := by
  intro h
  have k := payloadMap (inv up) (⟨0,by decide⟩ : Fin 1468)
  have bad : 6 ≤ 5 := leOfHom k
  omega
example (s : Side) : ¬ IsIso ((BlockUnits.staged S Y 1 s).map up) := by
  intro h
  let F := BlockUnits.staged S Y 1 s
  let m := mu S Y 1
  let c := isoWhiskerLeft (J S Y 1 s) (BlockCompositor.multiplicationSquare S Y 1) ≪≫ eqToIso (nativeContract S Y 1 s)
  have e := (NatIso.isIso_map_iff c up).mp (m.map_isIso (F.map up))
  exact noniso (isIso_of_reflects_iso up (evaluation S Y 1))
example : (grade _ _ ((J S Y 1 .left).obj p)).val.fst.1 = 0 := congrArg Prod.fst (nativeShape S Y 1 .left p)
example : (grade _ _ ((J S Y 1 .right).obj p)).val.snd.1 = 0 := congrArg Prod.snd (nativeShape S Y 1 .right p)
-- Empty at *which* base object? The two strict endpoint vertices are different.
example : (NativeBlocks.leftLeg S).obj ((grade _ _ ((J S Y 1 .left).obj p)).val.fst) = 1 :=
  key Y 1 (degeneracy S .left) (fun w : (pairSpan S).apex => (leftLeg S).obj w.fst) p
example : (NativeBlocks.rightLeg S).obj ((grade _ _ ((J S Y 1 .right).obj p)).val.snd) = 1468 :=
  key Y 1 (degeneracy S .right) (fun w : (pairSpan S).apex => (rightLeg S).obj w.snd) p
example : IsEmpty (BlockUnits.staged S Y 1 .left ⟶ target S Y 1 .right) :=
  ⟨fun a => (by decide : (0 : Nat) ≠ 3) (congrArg Prod.fst ((stagedShape S Y 1 .left p).symm.trans
    ((profile_map S Y 1 (a.app p)).trans (targetShape S Y 1 .right p))))⟩
-- Both unit laws after multiplication still give a comparison to the WRONG side.
example : Nonempty (BlockUnits.staged S Y 1 .left ⋙ mu S Y 1 ≅ target S Y 1 .right ⋙ mu S Y 1) :=
  ⟨afterStaged S Y 1 .left ≪≫ eqToIso ((targetErase S Y 1 .left).trans (targetErase S Y 1 .right).symm)⟩
end Directional213
