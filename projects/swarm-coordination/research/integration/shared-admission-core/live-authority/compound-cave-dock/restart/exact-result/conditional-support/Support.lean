import Mathlib
namespace HandoffSupport

def pack (exclude code : ℕ) : ℕ :=
  if code < exclude then code else code-1

def unpack (exclude octet : ℕ) : ℕ :=
  if octet < exclude then octet else octet+1

theorem exact (omitted value : ℕ) (allowed : value ≠ omitted) :
    unpack omitted (pack omitted value) = value := by
  unfold unpack pack
  split_ifs <;> omega

theorem fits_byte (omitted value : ℕ) (h : omitted ≤ 256)
    (v : value ≤ 256) (_allowed : value ≠ omitted) : pack omitted value < 256 := by
  unfold pack
  split_ifs <;> omega

theorem low_group_extension :
    unpack 255 (pack 255 256) = 256 ∧
    unpack 255 255 = 256 := by decide

theorem support_union (v : Fin 257) :
    v.val ≠ 255 ∨ v.val ≠ 256 := by
  by_cases h : v.val = 255
  · right
    omega
  · exact Or.inl h

end HandoffSupport
#print axioms HandoffSupport.exact
#print axioms HandoffSupport.fits_byte
#print axioms HandoffSupport.low_group_extension
#print axioms HandoffSupport.support_union
