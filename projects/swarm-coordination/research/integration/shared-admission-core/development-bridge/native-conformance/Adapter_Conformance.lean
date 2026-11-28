import Mathlib

namespace AdapterConformance

variable {C M R V A : Type}

/-- None is no arrival, not an arrived-but-empty observation. -/
def passes {H : Type}
    (observe : H → R → Option V) (serves : H → R → A → Prop)
    (route : R) (choose : V → A) : Prop :=
  ∀ h, ∃ v, observe h route = some v ∧ serves h route (choose v)

/-- The abstract family may overapproximate concrete support. A
concretely coupled map has to preserve the actual view, not just a
set of possible values for each constituent observation. -/
theorem adapter_sound
    (abs : C → M) (co : C → R → Option V) (mo : M → R → Option V)
    (cs : C → R → A → Prop) (ms : M → R → A → Prop)
    (route : R) (choose : V → A)
    (view : ∀ c, co c route = mo (abs c) route)
    (effect : ∀ c a, ms (abs c) route a → cs c route a)
    (ok : passes mo ms route choose) : passes co cs route choose := by
  intro c
  obtain ⟨v, hv, hs⟩ := ok (abs c)
  exact ⟨v, (view c).trans hv, effect c _ hs⟩

/-- Completeness only needs real negative witnesses for each excluded
action and unavailable route. Whole-state reconstruction is stronger. -/
theorem adapter_complete
    (co : C → R → Option V) (mo : M → R → Option V)
    (cs : C → R → A → Prop) (ms : M → R → A → Prop)
    (route : R) (choose : V → A)
    (missing : ∀ m, mo m route = none → ∃ c, co c route = none)
    (negative : ∀ m v a, mo m route = some v → ¬ ms m route a →
       ∃ c, co c route = some v ∧ ¬ cs c route a)
    (ok : passes co cs route choose) : passes mo ms route choose := by
  intro m
  cases hm : mo m route with
  | none =>
    obtain ⟨c, hc⟩ := missing m hm
    obtain ⟨v, hv, _⟩ := ok c
    simp [hc] at hv
  | some v =>
    refine ⟨v, rfl, ?_⟩
    by_contra bad
    obtain ⟨c, hv, hn⟩ := negative m v _ hm bad
    obtain ⟨v', hv', hs⟩ := ok c
    have he : v = v' := Option.some.inj (hv.symm.trans hv')
    exact hn (he ▸ hs)

/-- Losing action masks are exact for future constraints on a
fixed reached view, but say nothing about a new view partition. -/
def loses {H : Type} (observe : H → R → Option V)
    (serves : H → R → A → Prop) (r : R) (v : V) (a : A) : Prop :=
  ∃ h, observe h r = some v ∧ ¬ serves h r a

def binds (seenNamespace expectedNamespace seenKey expectedKey
    seenBasis expectedBasis seenEpoch expectedEpoch : Nat) : Prop :=
  seenNamespace = expectedNamespace ∧ seenKey = expectedKey ∧
  seenBasis = expectedBasis ∧ seenEpoch = expectedEpoch

/-- Freshness of a local physical sample is checked at effect cut.
Currency of an immutable old result uses its key/epoch, not the
transport age of the copy carrying that result. -/
def LiveDebit (sent effect limit : Nat) : Prop := sent ≤ effect ∧ effect - sent ≤ limit
def Fresh (sample lastChange effect : Nat) : Prop :=
  lastChange ≤ sample ∧ sample ≤ effect

theorem historical_token_valid_after_debit
    (cut : Nat) (before : 1 < cut) :
    binds 0 0 1 1 2 2 3 3 ∧ ¬ LiveDebit 0 cut 1 ∧ ¬ Fresh 0 1 cut := by
  unfold binds LiveDebit Fresh
  omega

end AdapterConformance
