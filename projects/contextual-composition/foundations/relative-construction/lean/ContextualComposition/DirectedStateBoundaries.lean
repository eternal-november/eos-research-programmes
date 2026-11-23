module

public import ContextualComposition.DirectedStateUniversal

/-! State labels detect irreversible slides and a new endomorphism at the unit state in the constant-terminal process example. -/

@[expose] public section
namespace ContextualComposition.DirectedStateBoundary

open CategoryTheory Opposite DirectedStateBalance
universe u v w d
variable {S : Type u} [Category.{v} S] (F : Diagram.{v,u,w,d} S)

def labels : DirectedStateBalance.Cocone F S where
  fiber i := (Functor.const _).obj i
  bal h := {app := fun _ => h, naturality := by intros; exact (Category.id_comp _).trans (Category.comp_id _).symm}
  unit _ := rfl
  comp h g _ := by simp

abbrev state : Balance F ⥤ S := (labels F).descend

theorem native_label {i : S} {x y : atPair F i i} (a : x ⟶ y) : (state F).map ((insertion F i).map a) = 𝟙 i :=
  (labels F).descend_generator (Edge.native a)

theorem slide_label {i j : S} (h : i ⟶ j) (x : atPair F j i) : (state F).map ((slide F h).app x) = h :=
  (labels F).descend_generator (Edge.slide h x)

theorem irreversible {i j : S} (h : i ⟶ j) (no : ¬IsIso h) (x : atPair F j i) : ¬IsIso ((slide F h).app x) := by
  intro inv
  have image := (state F).map_isIso ((slide F h).app x)
  exact no ((slide_label F h x) ▸ image)

abbrev terminalDiagram (S : Type u) [Category.{v} S] : Diagram S :=
  strict ((Functor.const (Sᵒᵖ × S)).obj (Cat.of (Discrete Unit)))

/-- The one-object state category with composition given by natural-number addition. -/
inductive oneState where | unitState
open oneState

instance : Category oneState where
  Hom _ _ := ℕ
  id _ := 0
  comp f g := f + g
  id_comp := Nat.zero_add
  comp_id := Nat.add_zero
  assoc := Nat.add_assoc

abbrev tick : unitState ⟶ unitState := (1 : ℕ)

theorem tick_irreversible : ¬ IsIso tick := by
  intro h
  have e := IsIso.hom_inv_id tick
  change (1 : ℕ) + (show ℕ from inv tick) = (0 : ℕ) at e
  omega

theorem unit_not_full : ¬(insertion (terminalDiagram oneState) unitState).Full := by
  intro full
  let F := terminalDiagram oneState
  let x : atPair F unitState unitState := ⟨()⟩
  obtain ⟨a,ha⟩ := (insertion F unitState).map_surjective (X := x) (Y := x) ((slide F tick).app x)
  have e := (native_label F a).symm.trans ((congrArg (state F).map ha).trans (slide_label F tick x))
  exact Nat.zero_ne_one e

end ContextualComposition.DirectedStateBoundary
