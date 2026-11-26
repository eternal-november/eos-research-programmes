import Lean

namespace QualifiedProbe
universe u v w
variable {W : Type u} {G : Type v} {Obs : Type w}

theorem silent_conflict (obs : W → Obs) (p f : W)
    (same : obs p = obs f) :
    ¬ ∃ choose : Obs → Bool, choose (obs p) = false ∧ choose (obs f) = true := by
  rintro ⟨chosen, a, b⟩
  rw [← same, a] at b
  contradiction

theorem physical_capacity {cap placed probe payload : Nat}
    (probeFits : placed+probe ≤ cap)
    (excess : cap < placed+probe+payload) :
    placed+probe ≤ cap ∧ ¬ (placed+probe+payload ≤ cap) := by omega

theorem qualified_product (canReport : W → Prop) (canExit : G → Prop)
    (Rw : Nonempty W) (Rg : Nonempty G) :
    (∀ w g, canReport w ∧ canExit g) ↔
    (∀ w, canReport w) ∧ (∀ g, canExit g) := by
  rcases Rw with ⟨w0⟩
  rcases Rg with ⟨g0⟩
  constructor
  · exact fun h => ⟨fun w => (h w g0).1,fun g => (h w0 g).2⟩
  · exact fun h w g => ⟨h.1 w,h.2 g⟩

#print axioms silent_conflict
#print axioms physical_capacity
#print axioms qualified_product
end QualifiedProbe
