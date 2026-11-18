import ContextualComposition.NativePacked
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativePacked NativeCleavage
namespace Boundary210
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
def one : tel S := ⟨1,pair P.grades (𝟭 B) b b⟩
def atom (a d : b ⟶ b) : one ⟶ one := (incl S 1).map (arrow (x := one.2) (y := one.2) a d)
def x : (pairSpan S).apex := ⟨one,one,rfl⟩
def boundary (m e : b ⟶ b) : x ⟶ x := ⟨⟨atom (𝟙 _) m,atom m e,rfl⟩⟩
example (h : x ⟶ x) (i : h.hom.fst = atom (𝟙 _) yes) (j : h.hom.snd = atom no yes) : False := by
  have k := h.hom.w; rw [i,j] at k; exact Bool.noConfusion (congrFun k false)
def X : (pairSpan S).source.Fiber b := ⟨x,rfl⟩
def z (m e : b ⟶ b) : X ⟶ X := ⟨boundary m e,IsHomLift.of_fac' _ _ _ rfl rfl rfl⟩
def Y : Bᵒᵖ ⥤ Cat.{0,0} where
  obj _ := Cat.of (Bool → Nat)
  map f := (Pi.comap (fun _ : Bool => Nat) (show Bool → Bool from f.unop)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
abbrev c := Lift.value Y b (pairSpan S)
def p : c := pair Y _ X (fun _ => 1)
def q : c := pair Y _ X (fun t => if t then 1 else 0)
def f (m : b ⟶ b) : p ⟶ q := arrow (z m yes) (fun _ => homOfLE (le_refl (1:Nat)))
example (m : b ⟶ b) : ¬ ∃ t : p ⟶ q, gradeMap t = z m no := by
  rintro ⟨t,ht⟩
  have h := payloadMap t; rw [ht] at h
  exact (by decide : ¬ 1 ≤ 0) (leOfHom (h false))
noncomputable abbrev A := (NativePacked.compare S Y b).functor ⋙ multiplication S Y b
noncomputable abbrev C := Lift.weighted (row S) Y b ⋙ FibreTotal.into Y (BlockCartesian.All.dest S) (BlockCartesian.All.source S) b ⋙
  BlockCartesian.All.onFibre S Y b ⋙ FibreTotal.out Y (rightLeg S) (leftLeg S) b ⋙ evaluation S Y b
def seeBoundary : c ⥤ B := gradeProjection ⋙ Functor.Fiber.fiberInclusion ⋙ SpanApex.Strict.fst _ _ ⋙ rightLeg S
theorem different : f yes ≠ f no := by
  intro h
  exact Bool.noConfusion (congrFun (congrArg seeBoundary.map h) false)
noncomputable abbrev α := actualSquare S Y b
-- The two arrows differ only at the internal cut, invisible to input/output endpoint observers.
example : (pairSpan S).source.map (gradeMap (f yes)).1 = (pairSpan S).source.map (gradeMap (f no)).1 := rfl
example : (pairSpan S).dest.map (gradeMap (f yes)).1 = (pairSpan S).dest.map (gradeMap (f no)).1 := rfl
example (m : b ⟶ b) : A.map (f m) ≫ α.hom.app q = α.hom.app p ≫ C.map (f m) := α.hom.naturality _
theorem packed_ne : A.map (f yes) ≠ A.map (f no) := by
  let _ : (multiplication S Y b).Faithful := BlockCartesian.faithful _ (PackedCuts.joinIncoming S Y b)
  exact fun h => different (A.map_injective h)
example : C.map (f yes) ≠ C.map (f no) := by
  intro h
  apply packed_ne
  exact (cancel_mono (α.hom.app q)).mp ((α.hom.naturality _).trans ((congrArg (α.hom.app p ≫ ·) h).trans (α.hom.naturality _).symm))
example : ¬ IsIso (f yes) := by
  intro h
  let _ := h
  have k := congrArg seeBoundary.map (IsIso.hom_inv_id (f yes))
  rw [seeBoundary.map_comp,seeBoundary.map_id] at k
  have ht := congrFun k true
  have hf := congrFun k false
  change (seeBoundary.map (inv (f yes))) true = true at ht
  change (seeBoundary.map (inv (f yes))) true = false at hf
  exact Bool.noConfusion (ht.symm.trans hf)
end Boundary210
