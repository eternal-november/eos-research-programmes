import ContextualComposition.BlockCompositor
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep PackedCuts
namespace Positions212
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
example : (cutEquiv S Y 1).functor.obj ⟨(0,3),path⟩ = cut₀ := rfl
example : (cutEquiv S Y 1).functor.obj ⟨(1,2),path⟩ = cut₁ := rfl
example : (cutEquiv S Y 1).functor.obj ⟨(2,1),path⟩ = cut₂ := rfl
example : (cutEquiv S Y 1).functor.obj ⟨(3,0),path⟩ = cut₃ := rfl
example : (mu S Y 1).obj cut₁ = x := Functor.congr_obj (cut_join_at S Y 1 (1,2)) path
example : (mu S Y 1).obj cut₃ = x := Functor.congr_obj (cut_join_at S Y 1 (3,0)) path


open CutCompositor BlockEvaluation NativePacked NativeBlocks NativeTrace WordTrace
abbrev z : (power S 3).apex := pair P.grades _ (pair P.grades _ (pair P.grades (𝟭 Nat) 1 (G 4)) (G 6)) (G 8)
def w : Total Y (power S 3).dest := pair Y _ z V
def q : Total Y (power S 3).dest := pair Y _ z (fun i => V i + 1)
def upw : w ⟶ q := arrow (𝟙 z) (fun _ => homOfLE (Nat.le_succ _))
def input : Edge (Total Y (power S 3).dest) := ⟨w,q,upw⟩
def before (g : Atom (P := P)) : Nat := grade _ _ g.src
def after (g : Atom (P := P)) : Nat := (SpanApex.right P S).obj g.src
def bounds (p : Trace (P := P) Y) : List (Nat × Nat) := p.1.map (fun g => (before g,after g))
noncomputable def raw := read S Y 3 (Edge.map (global S Y 3) input)
example : bounds raw = [(1,14),(14,146),(146,1468)] := by unfold raw; rw [read_global]; rfl
example : (read S Y 3 (Edge.map (global S Y 3) input)).2.src = pair Y (𝟭 Nat) 1468 V := by rw [read_global]; rfl
example : ¬ IsIso upw := by
  intro h
  let _ := h
  have e := payloadMap (inv upw) (⟨0,by decide⟩ : Fin 1468)
  have bad : 6 ≤ 5 := leOfHom e
  omega
-- The whole evaluated trace is identical for different cuts, but the native
-- cut projections retain WHICH moving contexts belong to each piece.
theorem cutTrace (n m : Nat) (z : Edge (Total Y (power S (n+m)).dest)) :
  flattenRead S Y n m (Edge.map (Lift.total (cut S (n,m)) Y ⋙ totalStages S Y n m) z) =
    read S Y (n+m) (Edge.map (global S Y (n+m)) z) := by
  have c := congrArg (fun F => flattenRead S Y n m (Edge.map F z)) (BlockCompositor.total S Y n m)
  have j := read_order S Y n m (Edge.map (BlockCompositor.transport (sameLength S Y (n,m)).symm) (Edge.map (global S Y (n+m)) z))
  rw [BlockCompositor.transport_edge,BlockCompositor.shift_cancel] at j
  exact c.trans ((congrArg (flattenRead S Y n m) (BlockCompositor.transport_edge (sameLength S Y (n,m)).symm (Edge.map (global S Y (n+m)) z))).trans j.symm)
example : bounds (flattenRead S Y 1 2 (Edge.map (Lift.total (cut S (1,2)) Y ⋙ totalStages S Y 1 2) input)) = [(1,14),(14,146),(146,1468)] := by rw [cutTrace,read_global]; rfl
example : bounds (flattenRead S Y 2 1 (Edge.map (Lift.total (cut S (2,1)) Y ⋙ totalStages S Y 2 1) input)) = [(1,14),(14,146),(146,1468)] := by rw [cutTrace,read_global]; rfl
example : first S Y 1 (0,3) = CutCompositor.second S Y 1 (0,3) := BlockCompositor.fixedCompositor S Y 1 0 3
example : first S Y 1 (3,0) = CutCompositor.second S Y 1 (3,0) := BlockCompositor.fixedCompositor S Y 1 3 0
theorem length_word : (n : Nat) → (e : Edge (power S n).apex) → (word S n e).length = n
  | 0,_ => rfl
  | n+1,e => by change (_ ++ [_]).length = _; simp [length_word n (Edge.map (NativeAssoc.front S n) e)]
theorem frontTrace (n m : Nat) (e : Edge (power S (n+m)).apex) :
    word S n (Edge.map (blocks S n m).first e) = (word S (n+m) e).take n := by
  rw [← word_cut S n m e]
  let p := word S n (Edge.map (blocks S n m).first e)
  let q := word S m (Edge.map (blocks S n m).rest e)
  exact (List.take_left (l₁ := p) (l₂ := q)).symm.trans (congrArg (fun k => (p++q).take k) (length_word n _))
noncomputable def frontEnds (n m : Nat) (g : Edge (power S (n+m)).apex) :=
  (word S n (Edge.map (blocks S n m).first g)).map after
example : frontEnds 1 2 (Edge.map gradeProjection input) = [14] := by unfold frontEnds; rw [frontTrace]; rfl
example : frontEnds 2 1 (Edge.map gradeProjection input) = [14,146] := by unfold frontEnds; rw [frontTrace]; rfl
end Positions212
