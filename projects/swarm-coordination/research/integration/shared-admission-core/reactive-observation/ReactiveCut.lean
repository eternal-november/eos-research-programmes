import Lean
namespace ReactiveCut

theorem common_selector {H O A : Type} (v : H → O) (ok : H → A → Prop)
    (seed : A) :
    (∃ p : O → A, ∀ h, ok h (p (v h))) ↔
      (∀ o, (∃ h, v h = o) → ∃ a, ∀ h, v h = o → ok h a) := by
  classical
  constructor
  · rintro ⟨p, hp⟩ o _
    exact ⟨p o, fun h hv => hv ▸ hp h⟩
  · intro support
    let p : O → A := fun o => if x : ∃ h, v h = o then Classical.choose (support o x) else seed
    refine ⟨p, ?_⟩
    intro h
    have x : ∃ h', v h' = v h := ⟨h, rfl⟩
    simp only [p, dite_eq_left x]
    exact Classical.choose_spec (support (v h) x) h rfl

-- Boolean true is clear/local; false is occupied/remote.
inductive Obs where
  | recv (b : Bool)
  | silent
deriving DecidableEq

def sensed (clear delivered : Bool) : Obs :=
  if delivered then .recv clear else .silent

theorem silence_exact (admit : Bool → Bool → Prop) :
    (∃ p : Obs → Bool, ∀ c d, admit c d → p (sensed c d) = c)
    ↔ ¬ (admit true false ∧ admit false false) := by
  classical
  constructor
  · rintro ⟨p,hp⟩ ⟨h₁,h₂⟩
    have a : p Obs.silent = true := hp true false h₁
    have b : p Obs.silent = false := hp false false h₂
    exact Bool.noConfusion (a.symm.trans b)
  · intro h
    refine ⟨fun o => match o with | .recv b => b | .silent => decide (admit true false), ?_⟩
    intro c d hc
    cases d
    · cases c
      · have notTrue : ¬ admit true false := fun ht => h ⟨ht,hc⟩
        simp [sensed,notTrue]
      · simp [sensed,hc]
    · simp [sensed]

-- A physically hosted idle is a separate cost even with the same view.
theorem one_idle_exact (clear deadline : Nat) :
    clear ≤ deadline ∧ ¬ (clear + 1 ≤ deadline) ↔ clear = deadline := by
  omega

-- The query's byte charge is persistent even if no reply evidence arrives.
theorem one_probe_reserve_exact (p debit due cap : Nat) (fits : p + due ≤ cap) :
    p + debit + due ≤ cap ↔ debit ≤ cap - (p + due) := by
  omega

#print axioms common_selector
#print axioms silence_exact
#print axioms one_idle_exact
#print axioms one_probe_reserve_exact
end ReactiveCut
