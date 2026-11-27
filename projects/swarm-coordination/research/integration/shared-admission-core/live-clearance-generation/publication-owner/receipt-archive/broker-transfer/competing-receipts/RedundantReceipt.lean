import Mathlib
namespace RedundantReceipt
def debit (cap used bytes : Nat) : Nat :=
  if used + bytes ≤ cap then used + bytes else used

-- A before A before B; conditions isolate exactly the duplicate admission band.
theorem duplicateCloses {a b cap : Nat} (aa : 2*a ≤ cap)
    (notAll : cap < 2*a+b) :
    debit cap (debit cap a a) b = 2*a := by
  have h1 : a+a ≤ cap := by omega
  have h2 : ¬ a+a+b ≤ cap := by omega
  simp [debit, h1, h2]
  omega

theorem rejectedDuplicateSpares {a b cap : Nat} (both : a+b ≤ cap)
    (notDup : cap < 2*a) : debit cap (debit cap a a) b = a+b := by
  have h1 : ¬ a+a ≤ cap := by omega
  simp [debit, h1, both]

theorem protectedDistinct {a b cap : Nat} (both : a+b ≤ cap) :
    debit cap (debit cap 0 a) b = a+b := by
  have h1 : a ≤ cap := by omega
  simp [debit, h1, both]

theorem weakBackupCannotFollow {a b cap : Nat} (h : cap < a+b) :
    debit cap b a = b := by
  have h1 : ¬ b+a ≤ cap := by omega
  simp [debit, h1]

#print axioms duplicateCloses
#print axioms rejectedDuplicateSpares
#print axioms protectedDistinct
#print axioms weakBackupCannotFollow
end RedundantReceipt