import SwarmTwoBayPolicyTables
import Mathlib.Logic.Equiv.Basic

namespace SwarmTwoBay

/-- Distinct projected compatibility relations, not pairs of implementation witnesses. -/
def Layouts (n : Nat) :=
  Set.range (@compatible (Fin (n + 1)))

def extendTail {n : Nat} (t : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cases false t

def normalize {n : Nat} (g : Fin (n + 1) → Bool) : Fin (n + 1) → Bool :=
  if g 0 then complement g else g

theorem normalize_head {n : Nat} (g : Fin (n + 1) → Bool) :
    normalize g 0 = false := by
  cases hg : g 0 <;> simp [normalize, complement, hg]

theorem normalize_compatible {n : Nat} (g : Fin (n + 1) → Bool) :
    compatible (normalize g) = compatible g := by
  cases hg : g 0 <;> simp [normalize, hg, compatible_complement]

def tailLayout {n : Nat} (t : Fin n → Bool) : Layouts n :=
  ⟨compatible (extendTail t), ⟨extendTail t, rfl⟩⟩

theorem tailLayout_bijective (n : Nat) : Function.Bijective (@tailLayout n) := by
  constructor
  · intro a b h
    have he : compatible (extendTail a) = compatible (extendTail b) := congrArg Subtype.val h
    rcases (compatible_eq_iff _ _).mp he with e | e
    · funext k
      exact congrFun e k.succ
    · have bad := congrFun e 0
      exact False.elim (Bool.false_ne_true bad)
  · rintro ⟨r, g, rfl⟩
    let t : Fin n → Bool := fun k => normalize g k.succ
    refine ⟨t, Subtype.ext ?_⟩
    change compatible (extendTail t) = compatible g
    rw [← normalize_compatible g]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact (normalize_head g).symm
    · rfl

/-- Fixing the first bit at false gives one representative per compatibility relation. -/
noncomputable def tailLayoutEquiv (n : Nat) : (Fin n → Bool) ≃ Layouts n :=
  Equiv.ofBijective tailLayout (tailLayout_bijective n)


#print axioms tailLayout_bijective
#print axioms tailLayoutEquiv
end SwarmTwoBay
