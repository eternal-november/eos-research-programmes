import Mathlib

namespace SharedFixture
def release (t q p : ℕ) := max t q + p

theorem release_order (t qi qj pi pj : ℕ) (h : qi ≤ qj) :
    release (release t qi pi) qj pj ≤ release (release t qj pj) qi pi := by
  unfold release
  have hu : max t qi ≤ max t qj := max_le_max_left t h
  have hv : qj ≤ max t qj := le_max_right .. 
  have hw : qi ≤ max t qj + pj := by omega
  rw [max_eq_left hw]
  rcases le_total (max t qi + pi) qj with a|a
  · rw [max_eq_right a]; omega
  · rw [max_eq_left a]; omega

def commit (h c L t : ℕ) := max (max h L) t + h + 2*c
def wait (h c L t : ℕ) := max (t + 2*h + c) L + c

theorem wait_strict (h c L t : ℕ) (hh : 0 < h) (hc : 0 < c) :
    wait h c L t < commit h c L t ↔ t+h < L := by
  unfold wait commit
  rcases le_total h L with a|a <;>
    rcases le_total (max h L) t with b|b <;>
    rcases le_total (t+2*h+c) L with d|d
  · rw [max_eq_right d, max_eq_right b]; rw [max_eq_right a] at b; omega
  · rw [max_eq_left d, max_eq_right b]; rw [max_eq_right a] at b; omega
  · rw [max_eq_right d, max_eq_left b, max_eq_right a]; omega
  · rw [max_eq_left d, max_eq_left b, max_eq_right a]; omega
  · rw [max_eq_right d, max_eq_right b]; omega
  · rw [max_eq_left d, max_eq_right b]; omega
  · rw [max_eq_right d, max_eq_left b, max_eq_left a]; omega
  · rw [max_eq_left d, max_eq_left b, max_eq_left a]; omega
end SharedFixture
#print axioms SharedFixture.release_order
#print axioms SharedFixture.wait_strict
