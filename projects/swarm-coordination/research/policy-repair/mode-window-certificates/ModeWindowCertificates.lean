import Mathlib

namespace SwarmModes

structure Window where
  lower : ℤ
  upper : ℤ

def Within (w : Window) (t : ℤ) : Prop :=
  w.lower ≤ t ∧ t ≤ w.upper

theorem mode_extrema_exact {History : Type} (w : History → Window)
    (lastStart firstEnd : History)
    (hlo : ∀ h, (w h).lower ≤ (w lastStart).lower)
    (hhi : ∀ h, (w firstEnd).upper ≤ (w h).upper) (t : ℤ) :
    (∀ h, Within (w h) t) ↔
      (w lastStart).lower ≤ t ∧ t ≤ (w firstEnd).upper := by
  constructor
  · intro h
    exact ⟨(h lastStart).1,(h firstEnd).2⟩
  · rintro ⟨hl,hh⟩ h
    exact ⟨le_trans (hlo h) hl, le_trans hh (hhi h)⟩

theorem incompatible_mode_witness
    {Mode History : Type} [Fintype Mode] [DecidableEq History]
    (w : Mode → History → Window) (lastStart firstEnd : Mode → History)
    (empty : ∀ m, (w m (firstEnd m)).upper < (w m (lastStart m)).lower) :
    ∃ s : Finset History, s.card ≤ 2 * Fintype.card Mode ∧
      (∀ m, ¬∃ t, ∀ h ∈ s, Within (w m h) t) := by
  let lo := Finset.univ.image lastStart
  let hi := Finset.univ.image firstEnd
  refine ⟨lo ∪ hi, ?_, ?_⟩
  · have hlo : lo.card ≤ Fintype.card Mode := by
      simpa [lo] using Finset.card_image_le (s := (Finset.univ : Finset Mode)) (f := lastStart)
    have hhi : hi.card ≤ Fintype.card Mode := by
      simpa [hi] using Finset.card_image_le (s := (Finset.univ : Finset Mode)) (f := firstEnd)
    rw [two_mul]
    exact (Finset.card_union_le lo hi).trans (Nat.add_le_add hlo hhi)
  · intro m
    rintro ⟨t,h⟩
    have a : lastStart m ∈ lo ∪ hi := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨m,Finset.mem_univ _,rfl⟩
    have b : firstEnd m ∈ lo ∪ hi := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨m,Finset.mem_univ _,rfl⟩
    exact (not_le_of_gt (empty m)) ((h _ a).1.trans (h _ b).2)

def hardWindows {Mode : Type} [DecidableEq Mode]
    (m : Mode) (h : Mode × Bool) : Window :=
  if h.1 ≠ m then ⟨0,1⟩
  else if h.2 then ⟨1,1⟩ else ⟨0,0⟩

theorem hard_full_conflict {Mode : Type} [DecidableEq Mode] (m : Mode) :
    ¬ ∃ t, ∀ h : Mode × Bool, Within (hardWindows m h) t := by
  rintro ⟨t,h⟩
  have h0 := h (m,false)
  have h1 := h (m,true)
  simp [Within, hardWindows] at h0 h1
  omega

theorem hard_any_omission_allows_action {Mode : Type} [DecidableEq Mode]
    (m : Mode) (b : Bool) :
    ∃ t, ∀ h : Mode × Bool, h ≠ (m,b) → Within (hardWindows m h) t := by
  refine ⟨if b then 0 else 1, ?_⟩
  rintro ⟨u,v⟩ huv
  by_cases h : u = m
  · subst u
    cases b <;> cases v <;> simp [Within, hardWindows] at *
  · cases b <;> simp [Within, hardWindows, h]

#print axioms mode_extrema_exact
#print axioms incompatible_mode_witness
#print axioms hard_full_conflict
#print axioms hard_any_omission_allows_action

theorem hard_no_smaller_certificate {Mode : Type}
    [Fintype Mode] [DecidableEq Mode] (s : Finset (Mode × Bool))
    (hs : s.card < 2 * Fintype.card Mode) :
    ∃ (m : Mode) (t : ℤ), ∀ h ∈ s, Within (hardWindows m h) t := by
  have miss : ∃ w : Mode × Bool, w ∉ s := by
    by_contra hn
    push Not at hn
    have eq : s = Finset.univ := by ext w; simp [hn w]
    rw [eq,Finset.card_univ,Fintype.card_prod] at hs
    simp [Nat.mul_comm] at hs
  obtain ⟨⟨m,b⟩,hm⟩ := miss
  obtain ⟨t,ht⟩ := hard_any_omission_allows_action m b
  refine ⟨m,t,fun h hmem => ht h ?_⟩
  intro e
  exact hm (e ▸ hmem)

theorem rejection_survives_replacement
    {Mode History : Type} (old new : Mode → History → Window)
    (certificate : Finset History) (admitted : Set History)
    (hcovered : ∀ h ∈ certificate, h ∈ admitted)
    (hsame : ∀ m h, h ∈ certificate → new m h = old m h)
    (hbad : ∀ m, ¬ ∃ t, ∀ h ∈ certificate, Within (old m h) t) :
    ¬ ∃ (m : Mode) (t : ℤ), ∀ h ∈ admitted, Within (new m h) t := by
  rintro ⟨m,t,hgood⟩
  apply hbad m
  refine ⟨t,fun h hh => ?_⟩
  simpa only [hsame m h hh] using hgood h (hcovered h hh)

#print axioms hard_no_smaller_certificate
#print axioms rejection_survives_replacement

theorem retain_rejection_by_two_endpoints_per_mode
    {Mode History : Type} (old new : Mode → History → Window)
    (ls rs : Mode → History) (admitted : Set History)
    (present : ∀ m, ls m ∈ admitted ∧ rs m ∈ admitted)
    (lowerTightens : ∀ m, (old m (ls m)).lower ≤ (new m (ls m)).lower)
    (upperTightens : ∀ m, (new m (rs m)).upper ≤ (old m (rs m)).upper)
    (oldImpossible : ∀ m, (old m (rs m)).upper < (old m (ls m)).lower) :
    ¬ ∃ (m : Mode) (t : ℤ), ∀ h ∈ admitted, Within (new m h) t := by
  rintro ⟨m,t,h⟩
  have hl := (h (ls m) (present m).1).1
  have hu := (h (rs m) (present m).2).2
  exact (not_le_of_gt (oldImpossible m))
    ((lowerTightens m).trans (hl.trans (hu.trans (upperTightens m))))

#print axioms retain_rejection_by_two_endpoints_per_mode
end SwarmModes
