import Mathlib

def removed {C P : Type} [DecidableEq P] (failed active : C → Prop)
    (declared : C → Finset P) (fallbackPorts : Finset P) (c : C) : Prop :=
  failed c ∨ (active c ∧ ¬ Disjoint (declared c) fallbackPorts)

theorem healthy_active_removed_iff {C P : Type} [DecidableEq P]
    (bad act : C → Prop) (ports : C → Finset P) (needed : Finset P) (c : C)
    (h : ¬ bad c) (a : act c) :
    removed bad act ports needed c ↔ ¬ Disjoint (ports c) needed := by
  simp [removed, h, a]

theorem separate_healthy_survives {C P : Type} [DecidableEq P]
    (bad act : C → Prop) (ports : C → Finset P) (needed : Finset P) (c : C)
    (h : ¬ bad c) (d : Disjoint (ports c) needed) :
    ¬ removed bad act ports needed c := by
  simp [removed, h, d]

#print axioms healthy_active_removed_iff
#print axioms separate_healthy_survives
