import ContextualComposition.MovingFrames
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep
open MovingCoordinates ChartRealization NativePacked
namespace ActualMoving
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
abbrev B := Nat
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of B)
def P : Endpoints.{0,0,0,0} B where
  grades := Y
  extend _ := 𝟭 B
  lift _ := 𝟙 _
theorem S : P.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := by apply heq_of_eq; apply Subsingleton.elim
abbrev i : Nat × Nat := (0,0)
noncomputable abbrev J := Lift.total (Lift.comp (NativePacked.cut S i) (NativePacked.tagged S i)) Y
abbrev z (k : B) : Q S Y i := pair Y _ k k
def step : (0:B) ⟶ (1:B) := homOfLE (show (0:B) ≤ 1 by decide)
def a : z 0 ⟶ z 1 := arrow step step
noncomputable abbrev f := J.map a
theorem graded (k : B) : (base S Y).obj (J.obj (z k)) = k :=
  Functor.congr_obj (Lift.over (Lift.comp (NativePacked.cut S i) (NativePacked.tagged S i)) Y) (z k)
theorem different : (base S Y).obj (J.obj (z 0)) ≠ (base S Y).obj (J.obj (z 1)) := by
  rw [graded,graded]; decide
example : ¬ IsIso ((base S Y).map f) := by
  intro h
  have k := leOfHom (inv ((base S Y).map f))
  rw [graded,graded] at k
  exact (by decide : ¬(1:B) ≤ 0) k
example := MovingCell.moving S Y f
end ActualMoving
