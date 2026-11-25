import Mathlib

def window (a b shift : Nat) : Nat :=
  ((a * 2^11 + b) / 2^(11-shift)) % 2^11

-- MSB-first 0/data/parity/11 words.
theorem periodic_S_to_j :
    window 0b01010011011 0b01010011011 8 = 0b01101010011 := by decide

theorem transition_space_apostrophe_to_r :
    window 0b00100000111 0b00100111011 7 = 0b01110010011 := by decide

theorem wrong_phase_single_flip :
    window 0b00000000011 0b00000001111 8 = 0b01100000001 ∧
    0b01100000001 + 2 = 0b01100000011 := by decide

theorem first_complete_frame_bound (cut : Nat) (h : cut < 11) :
    (if cut = 0 then 11 else 22-cut) ≤ 21 := by
  split <;> omega

#print axioms periodic_S_to_j
#print axioms transition_space_apostrophe_to_r
#print axioms wrong_phase_single_flip
#print axioms first_complete_frame_bound
