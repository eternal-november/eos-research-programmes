import Mathlib

namespace RetryOrder

theorem adjacent (p q s t : ℤ) (hq : 0 ≤ q)
    (prio : s-p ≥ t-q) : max s (p+t) ≤ max t (q+s) := by
  exact max_le (le_max_of_le_right (by omega)) (le_max_of_le_right (by omega))

theorem earlyCancelNotRelease (start ack physical next : ℕ)
    (before : next ≤ start+ack) (late : ack < physical) :
    next < start+physical := by omega

theorem oneShotAmbiguity (retry : Bool) :
    ∃ oldCommitted : Bool, ¬ ((oldCommitted || retry) && !(oldCommitted && retry)) := by
  cases retry
  · exact ⟨false,by decide⟩
  · exact ⟨true,by decide⟩

theorem robustNoCommonSupplier {W K : Type} (admitted : W → Prop)
    (ready : W → K → Prop)
    (miss : ∀ k, ∃ w, admitted w ∧ ¬ready w k) :
    ¬∃ k, ∀ w, admitted w → ready w k := by
  rintro ⟨k,h⟩
  obtain ⟨w,ha,hn⟩ := miss k
  exact hn (h w ha)

#print axioms adjacent
#print axioms earlyCancelNotRelease
#print axioms oneShotAmbiguity
#print axioms robustNoCommonSupplier
end RetryOrder
