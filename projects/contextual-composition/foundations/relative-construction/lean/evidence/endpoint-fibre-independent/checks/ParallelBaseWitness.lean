module
public import ContextualComposition.MovingFrames
@[expose] public section
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep MovingCoordinates ChartRealization NativePacked
namespace ParallelBaseWitness
inductive B where | star
instance : Category B where
  Hom _ _ := Nat
  id _ := 0
  comp f g := f + g
  id_comp := by intros; exact Nat.zero_add _
  comp_id := by intros; exact Nat.add_zero _
  assoc := by intros; exact Nat.add_assoc _ _ _
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of B)
def P : Endpoints.{0,0,0,0} B where
  grades := Y
  extend _ := 𝟭 B
  lift _ := 𝟙 _
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := by apply heq_of_eq; apply NatTrans.ext; rfl
abbrev i : Nat × Nat := (1,1)
noncomputable abbrev J := Lift.total (Lift.comp (NativePacked.cut S i) (NativePacked.tagged S i)) Y
abbrev z : Q S Y i := pair Y _ (pair P.grades _ (pair P.grades _ B.star B.star) B.star) B.star
def a (n : Nat) : z ⟶ z := arrow (arrow (arrow (show B.star ⟶ B.star from n) (0:Nat)) (0:Nat)) (0:Nat)
noncomputable abbrev f (n : Nat) := J.map (a n)
theorem weight {C : Type*} [Category* C] {F G : C ⥤ B} (h : F = G) {x y : C} (f : x ⟶ y) :
    (F.map f : Nat) = (G.map f : Nat) := by subst G; rfl
theorem baseWeight (n : Nat) : ((base S Y).map (f n) : Nat) = n :=
  weight (Lift.over (Lift.comp (NativePacked.cut S i) (NativePacked.tagged S i)) Y) (a n)
theorem distinct : (base S Y).map (f 1) ≠ (base S Y).map (f 2) := by
  intro e; have bad := (baseWeight 1).symm.trans (e.trans (baseWeight 2)); exact (by decide : (1:Nat) ≠ 2) bad
theorem notIso (n : Nat) (p : n ≠ 0) : ¬ IsIso ((base S Y).map (f n)) := by
  intro h
  have q := IsIso.hom_inv_id ((base S Y).map (f n))
  change Nat.add ((base S Y).map (f n)) (inv ((base S Y).map (f n))) = (0:Nat) at q
  exact p ((baseWeight n).symm.trans (Nat.add_eq_zero_iff.mp q).1)
end ParallelBaseWitness
