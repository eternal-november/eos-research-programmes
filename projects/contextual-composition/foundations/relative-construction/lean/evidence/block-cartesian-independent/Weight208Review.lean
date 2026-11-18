import ContextualComposition.BlockCartesian
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeCleavage BlockCartesian
namespace WeightReview
set_option backward.isDefEq.respectTransparency false
-- Terminal payload has genuine vertical arrows even when both native and nested grade words are empty.
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of (Discrete Unit))
  extend n := (Functor.const _).obj n
  lift f := { app := fun _ => f }
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def Y : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of Nat)
def zero (A : Nat) : strings S := ⟨0,A⟩
def singleton (A : Nat) : strings S := ⟨1,⟨0,A⟩⟩
def w0 (A n : Nat) := pair Y (All.dest S) (zero A) n
def w1 (A n : Nat) := pair Y (All.dest S) (singleton A) n
theorem cross (F : (w0 2 3) ⟶ (w1 2 3)) : False := by cases gradeMap F
def both {A D n k : Nat} (a : A ⟶ D) (h : n ≤ k) : w0 A n ⟶ w0 D k :=
  arrow ((outer S 0).map a) (show n ⟶ k from homOfLE h)
def obs : Total Y (All.dest S) ⥤ Nat where
  obj z := payload _ _ z
  map h := payloadMap h
  map_id _ := rfl
  map_comp _ _ := Subsingleton.elim _ _
def test : w0 2 3 ⟶ w0 5 9 := both (homOfLE (by decide)) (by decide)
-- No p-cartesian factor exists from the same grade source with payload 9, not merely noninvertibility.
theorem noncart : ¬ Cartesian (All.nestedProj S Y) test := by
  intro hc
  let j : w0 2 9 ⟶ w0 5 9 := both (homOfLE (by decide)) (by decide)
  obtain ⟨h,_,_⟩ := hc (w0 2 9) j (𝟙 (2:Nat)) (Subsingleton.elim _ _)
  exact (by decide : ¬ 9 ≤ 3) (leOfHom (obs.map h))
example : ¬ Cartesian (All.nativeProj S Y) ((All.weighted S Y).map test) :=
  fun hc => noncart ((All.weightedCartesian S Y test).mpr hc)
-- Bijectivity for incoming arrows also recovers this noncartesian lift, with its source.
example : liftInto (All.weighted S Y) (All.weightedIncoming S Y) (w0 5 9)
    (push (All.weighted S Y) ⟨w0 2 3,test⟩) = ⟨w0 2 3,test⟩ := by
  apply (All.weightedIncoming S Y _).injective
  apply push_liftInto
-- Lifts cannot be prescribed at an arbitrary object above the correct source.
theorem onPair {K L : Type*} [Category* K] [Category* L] (r : L ⥤ K) (d : K ⥤ Nat)
    {e : L ⥤ Nat} (h : r ⋙ d = e) (x : L) (n : Nat) :
    (SpanPayload.totalMap Y r d h).obj (pair Y e x n) = pair Y d (r.obj x) n := by subst e; rfl
theorem sameImage : (All.weighted S Y).obj (w0 2 3) = (All.weighted S Y).obj (w1 2 3) := by
  exact (onPair (flatten S) (rightLeg S) (flatten_dest S) (zero 2) 3).trans
    (onPair (flatten S) (rightLeg S) (flatten_dest S) (singleton 2) 3).symm
example : ¬ (All.weighted S Y).Full := by
  intro h; let := h
  exact cross ((All.weighted S Y).preimage (eqToHom sameImage))
end WeightReview
