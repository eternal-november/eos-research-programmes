import ContextualComposition.CutCompositor
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativePacked NativeCleavage
namespace Boundary211
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
-- All endpoints have the same object. Neither internal gluing nor terminal reindexing is detected by objects.
inductive B | pt
instance : Category B where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev b := B.pt
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 _
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def no : b ⟶ b := fun _ => false
def yes : b ⟶ b := fun _ => true
open BlockEvaluation SpanApex
def one : (power S 1).apex := pair P.grades (𝟭 B) b b
def atom (a d : b ⟶ b) : one ⟶ one := arrow a d
def x : (fixed S (1,1)).apex := ⟨one,one,rfl⟩
def boundary (a m e : b ⟶ b) : x ⟶ x := ⟨⟨atom a m,atom m e,rfl⟩⟩
example (h : x ⟶ x) (i : h.hom.fst = atom yes yes) (j : h.hom.snd = atom no yes) : False := by
  have k := h.hom.w; rw [i,j] at k; exact Bool.noConfusion (congrFun k false)
def Y : Bᵒᵖ ⥤ Cat.{0,0} where
  obj _ := Cat.of (Bool → Nat)
  map f := (Pi.comap (fun _ : Bool => Nat) (show Bool → Bool from f.unop)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
abbrev c := Total Y (fixed S (1,1)).dest
def p : c := pair Y _ x (fun _ => 1)
def q : c := pair Y _ x (fun t => if t then 1 else 0)
def f (m : b ⟶ b) : p ⟶ q := arrow (boundary no m yes) (fun _ => homOfLE (le_refl (1:Nat)))
example (m : b ⟶ b) : ¬ ∃ t : p ⟶ q, gradeMap t = boundary no m no := by
  rintro ⟨t,ht⟩
  have h := payloadMap t; rw [ht] at h
  exact (by decide : ¬ 1 ≤ 0) (leOfHom (h false))
-- No source-object or terminal-object test sees these differences; the two
-- weighted arrows even have the same external source and destination arrows.
def bound : c ⥤ B := gradeProjection ⋙ Strict.fst (power S 1).dest (power S 1).source ⋙ (power S 1).dest
def outside : c ⥤ B := gradeProjection ⋙ (fixed S (1,1)).source
example (m : b ⟶ b) : outside.map (f m) = no := rfl
example (m : b ⟶ b) : (fixed S (1,1)).dest.map (gradeMap (f m)) = yes := rfl
example (m : b ⟶ b) : bound.map (f m) = m := rfl
noncomputable def after := suffix S Y 1 1 ⋙ gradeProjection ⋙ (power S 1).dest
theorem observation : after = bound := congrArg (· ⋙ (power S 1).dest) (suffix_grade S Y 1 1)
example : after.map (f yes) ≠ after.map (f no) := by
  rw [observation]; exact fun e => Bool.noConfusion (congrFun e false)
example (m : b ⟶ b) : TelescopeSquares.Aligned ((suffix S Y 1 1 ⋙ second (BoundaryPaste.projectionData (out S Y 1)) (power S 1).dest).map (f m))
    ((SpanPayload.totalMap Y (Strict.snd (power S 1).dest (power S 1).source) (power S 1).dest rfl ⋙ global S Y 1).map (f m)) :=
  NativeCube.functorAlign (suffix_boundary S Y 1 1) _
example : (totalStages S Y 1 1).map (f yes) ≠ (totalStages S Y 1 1).map (f no) := by
  let _ := totalIso S Y 1 1
  apply fun e => Bool.noConfusion (congrFun (congrArg bound.map ((totalStages S Y 1 1).map_injective e)) false)
example : ¬ IsIso (f yes) := by
  intro hf; let _ := hf
  have h := congrArg outside.map (IsIso.hom_inv_id (f yes))
  rw [outside.map_comp,outside.map_id] at h
  have ht := congrFun h true
  have hf := congrFun h false
  change (outside.map (inv (f yes))) false = true at ht
  change (outside.map (inv (f yes))) false = false at hf
  exact Bool.noConfusion (ht.symm.trans hf)
end Boundary211
