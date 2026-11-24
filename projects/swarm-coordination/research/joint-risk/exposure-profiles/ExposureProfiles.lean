import Mathlib

namespace SwarmJointRisk

abbrev Exposure (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

theorem insertion_admitted_iff_mem (n k : ℕ) (s : Exposure n k) (q : Fin n) :
    (insert q s.1).card ≤ k ↔ q ∈ s.1 := by
  by_cases h : q ∈ s.1
  · simp [h, s.2]
  · simp [h, Finset.card_insert_of_notMem, s.2]

theorem exact_budget_decoder_injective (n k : ℕ) {Code : Type}
    (encode : Exposure n k → Code) (admit : Code → Fin n → Prop)
    (correct : ∀ s q, admit (encode s) q ↔ (insert q s.1).card ≤ k) :
    Function.Injective encode := by
  intro s t h
  apply Subtype.ext
  ext q
  rw [← insertion_admitted_iff_mem n k s q, ← insertion_admitted_iff_mem n k t q,
      ← correct s q, ← correct t q, h]

theorem exact_budget_decoder_cardinality (n k : ℕ) {Code : Type}
    [Fintype Code] (encode : Exposure n k → Code) (admit : Code → Fin n → Prop)
    (correct : ∀ s q, admit (encode s) q ↔ (insert q s.1).card ≤ k) :
    Fintype.card (Exposure n k) ≤ Fintype.card Code :=
  Fintype.card_le_of_injective encode (exact_budget_decoder_injective n k encode admit correct)


theorem exposure_card (n k : ℕ) :
    Fintype.card (Exposure n k) = Nat.choose n k := by
  classical
  let target := Finset.powersetCard k (Finset.univ : Finset (Fin n))
  let e : Exposure n k ≃ ↥target :=
    { toFun := fun s => ⟨s.1, Finset.mem_powersetCard_univ.mpr s.2⟩
      invFun := fun s => ⟨s.1, Finset.mem_powersetCard_univ.mp s.2⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  unfold target
  rw [Finset.card_powersetCard]
  simp

def mass {n : ℕ} (atom spike : ℝ) (s : Finset (Fin n)) (j : Fin n) : ℝ :=
  atom * s.card + if j ∈ s then spike else 0

theorem sharp_upper_mass {n : ℕ} (atom spike cap : ℝ)
    (s : Finset (Fin n)) (hs : s.Nonempty) (hw : 0 ≤ spike) :
    (∀ j, mass atom spike s j ≤ cap) ↔ atom * s.card + spike ≤ cap := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := hs
    simpa [mass, hj] using h j
  · intro h j
    by_cases hj : j ∈ s
    · simpa [mass, hj] using h
    · unfold mass
      rw [ite_eq_right hj]
      linarith

theorem robust_admission_iff_membership (n k : ℕ) (atom spike : ℝ)
    (ha : 0 < atom) (hw : 0 ≤ spike) (s : Exposure n k) (q : Fin n) :
    (∀ j, mass atom spike (insert q s.1) j ≤ atom * k + spike) ↔ q ∈ s.1 := by
  rw [sharp_upper_mass atom spike _ _ ⟨q, Finset.mem_insert_self q s.1⟩ hw]
  rw [← insertion_admitted_iff_mem n k s q]
  constructor
  · intro h
    have h' : ((insert q s.1).card : ℝ) ≤ k := by
      apply (mul_le_mul_iff_of_pos_left ha).mp
      linarith
    exact_mod_cast h'
  · intro h
    have h' : ((insert q s.1).card : ℝ) ≤ k := by exact_mod_cast h
    linarith [mul_le_mul_of_nonneg_left h' (le_of_lt ha)]

theorem robust_summary_state_lower_bound (n k : ℕ) (atom spike : ℝ)
    (ha : 0 < atom) (hw : 0 ≤ spike) {Code : Type} [Fintype Code]
    (encode : Exposure n k → Code) (admit : Code → Fin n → Prop)
    (correct : ∀ s q, admit (encode s) q ↔
      ∀ j, mass atom spike (insert q s.1) j ≤ atom * k + spike) :
    Nat.choose n k ≤ Fintype.card Code := by
  rw [← exposure_card n k]
  apply exact_budget_decoder_cardinality n k encode admit
  intro s q
  rw [correct, robust_admission_iff_membership n k atom spike ha hw,
      insertion_admitted_iff_mem n k s q]

#print axioms exposure_card
#print axioms robust_admission_iff_membership
#print axioms robust_summary_state_lower_bound

theorem unreviewed_future_queries_lose_old_profile
    (n k : ℕ) (atom spike : ℝ) (ha : 0 < atom) (hw : 0 ≤ spike)
    (s : Exposure n k) (q : Fin n) :
    (∀ j, mass atom spike (insert q s.1) j ≤ atom * (k+1) + spike) ∧
    ((∀ j, mass atom spike (insert q s.1) j ≤ atom * k + spike) ↔ q ∈ s.1) := by
  constructor
  · apply (sharp_upper_mass atom spike _ _ ⟨q, Finset.mem_insert_self q s.1⟩ hw).mpr
    have hN : (insert q s.1).card ≤ k+1 := by
      by_cases hq : q ∈ s.1
      · rw [Finset.insert_eq_of_mem hq, s.2]
        omega
      · rw [Finset.card_insert_of_notMem hq, s.2]
    have hR : ((insert q s.1).card : ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast hN
    linarith [mul_le_mul_of_nonneg_left hR (le_of_lt ha)]
  · exact robust_admission_iff_membership n k atom spike ha hw s q

#print axioms unreviewed_future_queries_lose_old_profile
end SwarmJointRisk
