import ContextualComposition.NativePacked
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep
namespace Cuts
set_option maxHeartbeats 400000
-- Native grades and their nonidentity arrows genuinely change the extended context.
def extend (a : Nat) : Nat ⥤ Nat where
  obj k := a+k
  map h := homOfLE (Nat.add_le_add_left h.le a)
  map_id _ := rfl
  map_comp _ _ := rfl
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend := extend
  lift {a d} f := { app := fun k => homOfLE (Nat.add_le_add_right f.le k) }
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := HEq.rfl
-- A nonthin terminal payload category: arrow labels retain an ordered word.
inductive Letter | pt
instance : Category Letter where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intro; intros; apply List.nil_append
  comp_id := by intro; intros; apply List.append_nil
  assoc := by intro; intros; apply List.append_assoc
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj a := Cat.of (Fin a.unop → Letter)
  map {a _} f := (Pi.comap (fun _ : Fin a.unop => Letter) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
abbrev L (n : Nat) := PackedFree.pow S Y n
def tail (k l : Nat) : (L 2).obj (op k) := pair _ _ l (pair _ _ (4 : Nat) (fun _ => Letter.pt))
def nested (a k l : Nat) : (PackedFree.pow S (L 2) 1).obj (op a) := pair _ _ k (tail (a+k) l)
abbrev x := nested 2 1 2
def word : (PackedFree.pow S Y 3).obj (op 2) := x
noncomputable def u := (PackedCuts.cutEquiv S Y 2).functor.obj ⟨(1,2),word⟩
noncomputable def v := (PackedCuts.cutEquiv S Y 2).functor.obj ⟨(2,1),word⟩
abbrev flat := PackedCuts.mu S Y 2
def out := (Iterates.inclusion P S Y 3 (op 2)).obj word
example : (grade _ _ out.2,grade _ _ (payload _ _ out.2),grade _ _ (payload _ _ (payload _ _ out.2))) = ((1:Nat),(2:Nat),(4:Nat)) := rfl
example : flat.obj u = out := Functor.congr_obj (PackedCuts.cut_join_at S Y 2 (1,2)) word
example : flat.obj v = out := Functor.congr_obj (PackedCuts.cut_join_at S Y 2 (2,1)) word
example (f : u ⟶ v) : False := by
  have e := ((PackedCuts.profile_at S Y 2 (1,2) word).symm.trans (PackedCuts.profile_map S Y 2 f)).trans (PackedCuts.profile_at S Y 2 (2,1) word)
  exact (by decide : (1,2) ≠ ((2,1) : Nat × Nat)) e
noncomputable example : {y // flat.obj y = out} ≃ Fin 4 := (PackedCuts.cutFibre S Y 2 out).trans (PackedCuts.positions S Y 2 out)
def nilPath := (Iterates.inclusion P S Y 0 (op 2)).obj (fun _ => Letter.pt)
noncomputable example : {y // flat.obj y = nilPath} ≃ Fin 1 := (PackedCuts.cutFibre S Y 2 nilPath).trans (PackedCuts.positions S Y 2 nilPath)
open NativeBlocks NativeBlocks.Nested
-- Two distinct unrestricted native row shapes both have empty concatenation.
def r0 : strings S := ⟨0,(2:Nat)⟩
def r1 : strings S := ⟨1,⟨0,(2:Nat)⟩⟩
example : (flatten S).obj r0 = (flatten S).obj r1 := rfl
theorem noArrow (f : r0 ⟶ r1) : False := by cases f
-- Any functor from the unrestricted native rows that sends BOTH these rows to
-- cuts above the same actual empty packed word cannot be full.
example (H : strings S ⥤ Iterates.Packed P S ((PackedFree.free S).obj Y) (op 2))
    (h : flat.obj (H.obj r0) = nilPath) (k : flat.obj (H.obj r1) = nilPath) : ¬ H.Full := by
  intro hf; let := hf
  have e := PackedCuts.zero_ext S Y 2 (h.trans k.symm) (congrArg Sigma.fst h)
  exact noArrow (H.preimage (eqToHom e))
-- The obstruction survives on the actual weighted fixed-source fibre and does
-- not assume equality of output objects: a single output arrow suffices.
abbrev Rows := NativeAssoc.Three.rows S
def t0 : Rows.source.Fiber 2 := ⟨r0,rfl⟩
def t1 : Rows.source.Fiber 2 := ⟨r1,rfl⟩
abbrev W := NativePacked.Lift.value Y 2 Rows
def w0 : W := pair Y _ t0 (fun _ => Letter.pt)
def w1 : W := pair Y _ t1 (fun _ => Letter.pt)
theorem weightedNoArrow (f : w0 ⟶ w1) : False := noArrow (gradeMap f).1
theorem notFull (H : W ⥤ Iterates.Packed P S ((PackedFree.free S).obj Y) (op 2))
    (zero : (flat.obj (H.obj w0)).1 = 0) (f : flat.obj (H.obj w0) ⟶ flat.obj (H.obj w1)) : ¬ H.Full := by
  intro hf; let := hf
  obtain ⟨⟨z,k⟩,eq⟩ := (PackedCuts.joinIncoming S Y 2 (H.obj w1)).surjective ⟨flat.obj (H.obj w0),f⟩
  have e : flat.obj z = flat.obj (H.obj w0) := congrArg Sigma.fst eq
  have h := PackedCuts.zero_ext S Y 2 e.symm zero
  exact weightedNoArrow (H.preimage (eqToHom h ≫ k))
theorem sameTag {x y : Iterates.Packed P S Y (op 2)} (f : x ⟶ y) : x.1 = y.1 := by cases f; rfl
example (H : W ⥤ Iterates.Packed P S ((PackedFree.free S).obj Y) (op 2))
    (i : flat.obj (H.obj w0) ≅ nilPath) (j : flat.obj (H.obj w1) ≅ nilPath) : ¬ H.Full :=
  notFull H (sameTag i.hom) (i.hom ≫ j.inv)
end Cuts
