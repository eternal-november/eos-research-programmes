import Mathlib

namespace SwarmAnonymousReserve

variable {α : Type} [DecidableEq α]

def down (Y : Set (Finset α)) : Set (Finset α) :=
  {s | ∃ y ∈ Y, s ⊆ y}

def safe (Y : Set (Finset α)) (W : Finset α) (b : ℕ) : Prop :=
  ∀ y ∈ Y, (W ∩ y).card ≤ b

theorem refine_of_down {Y Z : Set (Finset α)} (h : down Y ⊆ down Z)
    {W : Finset α} {b : ℕ} (hc : safe Z W b) : safe Y W b := by
  intro y hy
  have hy' : y ∈ down Y := ⟨y, hy, Finset.Subset.refl y⟩
  obtain ⟨z, hz, hsub⟩ := h hy'
  apply le_trans _ (hc z hz)
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hW, hY⟩ := Finset.mem_inter.mp ha
  exact Finset.mem_inter.mpr ⟨hW, hsub hY⟩

theorem down_of_refine {Y Z : Set (Finset α)} (hz : Z.Nonempty)
    (h : ∀ W b, safe Z W b → safe Y W b) : down Y ⊆ down Z := by
  classical
  intro s hs
  obtain ⟨y, hy, hyS⟩ := hs
  by_contra hbad
  have hne : s ≠ ∅ := by
    intro h0
    obtain ⟨z, hz'⟩ := hz
    apply hbad
    exact ⟨z, hz', h0 ▸ Finset.empty_subset z⟩
  have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hsafe : safe Z s (s.card - 1) := by
    intro z hz'
    have hstrict : s ∩ z ⊂ s := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro he
      apply hbad
      refine ⟨z, hz', ?_⟩
      intro a ha
      have ha' : a ∈ s ∩ z := he.symm ▸ ha
      exact (Finset.mem_inter.mp ha').2
    have hh := Finset.card_lt_card hstrict
    omega
  have hlim := h s (s.card - 1) hsafe y hy
  rw [Finset.inter_eq_left.mpr hyS] at hlim
  omega

theorem all_reserve_queries_iff {Y Z : Set (Finset α)} (hy : Y.Nonempty) (hz : Z.Nonempty) :
    (∀ W b, safe Y W b ↔ safe Z W b) ↔ down Y = down Z := by
  constructor
  · intro h
    apply Set.Subset.antisymm
    · exact down_of_refine hz (fun W b => (h W b).mpr)
    · exact down_of_refine hy (fun W b => (h W b).mp)
  · intro h W b
    constructor
    · exact refine_of_down (le_of_eq h.symm)
    · exact refine_of_down (le_of_eq h)

#print axioms refine_of_down
#print axioms down_of_refine
#print axioms all_reserve_queries_iff
end SwarmAnonymousReserve
