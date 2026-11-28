import Mathlib

namespace SwarmStaging

variable {H V : Type}

/-- The view is the full local stream through the cut, not a source history. -/
def Same (view : H → ℕ → V) (h k : H) (t : ℕ) : Prop :=
  ∀ u, u ≤ t → view h u = view k u

def Safe (view : H → ℕ → V) (allowed : H → ℕ → Prop) (h : H) (t : ℕ) :=
  ∀ k, Same view h k t → allowed k t

def Causal (view : H → ℕ → V) (act : H → ℕ) :=
  ∀ h k, Same view h k (act h) → act k = act h

theorem same_mono {view : H → ℕ → V} {h k : H} {u t : ℕ}
    (e : Same view h k t) (hu : u ≤ t) : Same view h k u :=
  fun v hv => e v (le_trans hv hu)

theorem safe_same {view : H → ℕ → V} {allowed : H → ℕ → Prop}
    {h k : H} {t : ℕ} (e : Same view h k t) :
    Safe view allowed h t ↔ Safe view allowed k t := by
  constructor
  · intro hh j ej
    exact hh j (fun u hu => (e u hu).trans (ej u hu))
  · intro hk j ej
    exact hk j (fun u hu => (e u hu).symm.trans (ej u hu))

theorem needed {view : H → ℕ → V} {allowed : H → ℕ → Prop}
    {act : H → ℕ} (c : Causal view act) (wins : ∀ h, allowed h (act h)) :
    ∀ h, Safe view allowed h (act h) := by
  intro h k e
  rw [← c h k e]
  exact wins k

theorem firstSafe {view : H → ℕ → V} {allowed : H → ℕ → Prop}
    (possible : ∀ h, ∃ t, Safe view allowed h t) :
    ∃ act : H → ℕ, Causal view act ∧ (∀ h, allowed h (act h)) ∧
      (∀ other : H → ℕ, Causal view other → (∀ h, allowed h (other h)) →
        ∀ h, act h ≤ other h) := by
  classical
  let act := fun h => Nat.find (possible h)
  have good (h : H) : Safe view allowed h (act h) := Nat.find_spec (possible h)
  have least (h : H) (u : ℕ) (hu : Safe view allowed h u) : act h ≤ u :=
    Nat.find_min' _ hu
  refine ⟨act, ?_, ?_, ?_⟩
  · intro h k eqv
    have l : act k ≤ act h := least k _ ((safe_same eqv).mp (good h))
    have r : act h ≤ act k := least h _ ((safe_same (same_mono eqv l)).mpr (good k))
    exact le_antisymm l r
  · intro h
    exact good h h (fun _ _ => rfl)
  · intro other c w h
    exact least h _ (needed c w h)

theorem receiptWindow {p r b lo hi : ℕ} (r_after : p ≤ r) (positive : 0 < lo)
    (proper : lo ≤ hi) :
    (∀ l, lo ≤ l → l ≤ hi → p < r + l ∧ r + l ≤ b) ↔ r + hi ≤ b := by
  constructor
  · intro f
    exact (f hi proper (le_refl hi)).2
  · intro h l ll hh
    omega

theorem localDelayObstruction
    {view : Bool → ℕ → V} (blind : Same view false true 1) :
    ¬ ∃ act : Bool → ℕ, Causal view act ∧ act false = 1 ∧ act true = 3 := by
  rintro ⟨act,hc,hf,ht⟩
  have e : Same view false true (act false) := by rw [hf]; exact blind
  have eq := hc false true e
  omega

#print axioms firstSafe
#print axioms receiptWindow
#print axioms localDelayObstruction
end SwarmStaging
