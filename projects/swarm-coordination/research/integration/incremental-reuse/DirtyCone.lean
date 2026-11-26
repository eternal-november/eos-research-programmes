import Mathlib

namespace DirtyCone
variable {V : Type*}

def Reach (edge : V → V → Prop) (root : V → Prop) (v : V) : Prop :=
  ∃ u, root u ∧ Relation.ReflTransGen edge u v

def Closed (D : V → Prop) (edge : V → V → Prop) : Prop :=
  ∀ ⦃u v⦄, edge u v → D u → D v

theorem stays (D : V → Prop) (edge : V → V → Prop)
    (close : Closed D edge) {u v : V}
    (run : Relation.ReflTransGen edge u v) (hu : D u) : D v := by
  induction run with
  | refl => exact hu
  | tail p e ih => exact close e ih

theorem copyOutside (D : V → Prop) (old new : V → V → Prop)
    (close : Closed D old)
    (same : ∀ ⦃u v⦄, ¬ D v → old u v → new u v)
    {u v : V} (run : Relation.ReflTransGen old u v) (outside : ¬ D v) :
    Relation.ReflTransGen new u v := by
  induction run with
  | refl => exact .refl
  | tail p e ih =>
      exact (ih (fun h => outside (close e h))).tail (same outside e)

theorem reachOutside (D : V → Prop) (old new : V → V → Prop)
    (a b : V → Prop) (co : Closed D old) (cn : Closed D new)
    (sameEdge : ∀ ⦃u v⦄, ¬ D v → (old u v ↔ new u v))
    (sameRoot : ∀ ⦃u⦄, ¬ D u → (a u ↔ b u))
    {v : V} (outside : ¬ D v) :
    Reach old a v ↔ Reach new b v := by
  constructor
  · rintro ⟨root, h, run⟩
    have nr : ¬ D root := fun h => outside (stays D old co run h)
    exact ⟨root, (sameRoot nr).mp h,
      copyOutside D old new co (fun {_ _} p e => (sameEdge p).mp e) run outside⟩
  · rintro ⟨root, h, run⟩
    have nr : ¬ D root := fun h => outside (stays D new cn run h)
    exact ⟨root, (sameRoot nr).mpr h,
      copyOutside D new old cn (fun {_ _} p e => (sameEdge p).mpr e) run outside⟩

def Seed (D : V → Prop) (edge : V → V → Prop) (root : V → Prop) (v : V) : Prop :=
  D v ∧ (root v ∨ ∃ u, ¬D u ∧ Reach edge root u ∧ edge u v)

theorem enterInside (D : V → Prop) (edge : V → V → Prop) (root : V → Prop)
   {v : V} (inside : D v) :
    Reach edge root v ↔ Reach (fun u v => D u ∧ D v ∧ edge u v) (Seed D edge root) v := by
  constructor
  · rintro ⟨i, hi, path⟩
    induction path with
    | refl => exact ⟨i, ⟨inside, Or.inl hi⟩, .refl⟩
    | @tail u v p e ih =>
      by_cases h : D u
      · obtain ⟨a, ha, q⟩ := ih h
        exact ⟨a, ha, q.tail ⟨h, inside, e⟩⟩
      · exact ⟨v, ⟨inside, Or.inr ⟨u, h, ⟨i, hi, p⟩, e⟩⟩, .refl⟩
  · rintro ⟨u, ⟨hu, seed⟩, path⟩
    have pref : Reach edge root u := by
      rcases seed with h | ⟨v, _, ⟨i, hi, p⟩, e⟩
      · exact ⟨u, h, .refl⟩
      · exact ⟨i, hi, p.tail e⟩
    obtain ⟨i, hi, p⟩ := pref
    have inc : (fun u v => D u ∧ D v ∧ edge u v) ≤ edge := by
      intro _ _ h
      exact h.2.2
    exact ⟨i, hi, p.trans (Relation.ReflTransGen.mono inc u v path)⟩

end DirtyCone

#print axioms DirtyCone.reachOutside
#print axioms DirtyCone.enterInside
