import Lean
namespace TimedReceipt

theorem witness (base first last life : Nat) (forward : last ≤ base+first) :
    (∃ spacing emitted accepted age : Nat,
      base ≤ spacing ∧ emitted ≤ last ∧ first ≤ accepted ∧
      spacing+accepted = emitted+age ∧ age ≤ life) ↔
    base+first ≤ last+life := by
  constructor
  · rintro ⟨d,e,f,a,hd,he,hf,hs,ha⟩
    omega
  · intro h
    refine ⟨base,last,first,base+first-last,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,?_,?_⟩ <;> omega

theorem strict_witness (base first last life : Nat) (forward : last ≤ base+first) :
    (∃ spacing emitted accepted age : Nat,
      base ≤ spacing ∧ emitted ≤ last ∧ first ≤ accepted ∧
      spacing+accepted = emitted+age ∧ age < life) ↔
    base+first < last+life := by
  constructor
  · rintro ⟨d,e,f,a,hd,he,hf,hs,ha⟩
    omega
  · intro h
    refine ⟨base,last,first,base+first-last,Nat.le_refl _,Nat.le_refl _,Nat.le_refl _,?_,?_⟩ <;> omega

theorem common_later_conflict (startJ startK expiryI : Nat)
    (ordered : startJ ≤ startK) (live : startK ≤ expiryI) :
    startJ ≤ expiryI := Nat.le_trans ordered live

#print axioms witness
#print axioms strict_witness
#print axioms common_later_conflict
end TimedReceipt
