import Mathlib
namespace ScoreLog
def lookup (f : Fin 48) (q : Fin 48) := decide (f = q)
theorem recoversKey {k : Nat} (encode : Fin 48 → Fin (2^k))
    (dec : Fin (2^k) → Fin 48 → Bool)
    (valid : ∀ f q, dec (encode f) q = lookup f q) :
    Function.Injective encode := by
  intro a b ab
  have x := valid a a
  rw [ab, valid b a] at x
  simpa [lookup, eq_comm] using x

theorem atLeastSix {k : Nat} (encode : Fin 48 → Fin (2^k))
    (dec : Fin (2^k) → Fin 48 → Bool)
    (valid : ∀ f q, dec (encode f) q = lookup f q) : 6 ≤ k := by
  have h := Fintype.card_le_of_injective encode (recoversKey encode dec valid)
  simp only [Fintype.card_fin] at h
  by_contra! small
  have bound : 2^k ≤ (2:Nat)^5 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

def useSix (f : Fin 48) : Fin 64 := ⟨f.val, by omega⟩
def readSix (v : Fin 64) (q : Fin 48) : Bool := decide (v.val = q.val)
theorem sixSuffices (f q : Fin 48) : readSix (useSix f) q = lookup f q := by
  by_cases h : f = q
  · subst q
    simp [readSix, useSix, lookup]
  · have hv : f.val ≠ q.val := fun v => h (Fin.ext v)
    simp [readSix, useSix, lookup, h, hv]

def visibleCut (t : Nat) := (2 ≤ t, 4 ≤ t)
def memoryEffect (t : Nat) := 3 ≤ t
theorem sameArchiveDifferentEffect :
    visibleCut 2 = visibleCut 3 ∧ ¬memoryEffect 2 ∧ memoryEffect 3 := by
  simp [visibleCut,memoryEffect]
#print axioms recoversKey
#print axioms atLeastSix
#print axioms sameArchiveDifferentEffect
#print axioms sixSuffices
end ScoreLog
