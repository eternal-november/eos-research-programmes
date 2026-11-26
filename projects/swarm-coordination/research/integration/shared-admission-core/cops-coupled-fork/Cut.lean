import Lean
namespace ForkCut
inductive Start where
  | stay | near | far | stage
deriving DecidableEq

def feasible (staging branch : Bool) : Start → Prop
  | .stay => branch=false
  | .near => branch=false
  | .far => branch=true
  | .stage => staging=true

theorem unique_common_prefix (staging : Bool) (s : Start) :
    (∀ branch, feasible staging branch s) ↔ staging=true ∧ s=Start.stage := by
  constructor
  · intro h
    have left := h false
    have right := h true
    cases s <;> simp [feasible] at *
    exact left
  · rintro ⟨rfl,rfl⟩ b
    simp [feasible]

theorem no_common_second (known : Bool) :
    (∃ f : Bool → Bool, ∀ b : Bool, f (if known then b else false) = b)
    ↔ known=true := by
  constructor
  · rintro ⟨f,h⟩
    cases known
    · have a : f false = false := h false
      have b : f false = true := h true
      exact Bool.noConfusion (a.symm.trans b)
    · rfl
  · rintro rfl
    exact ⟨id,fun _ => rfl⟩

#print axioms unique_common_prefix
#print axioms no_common_second
end ForkCut
