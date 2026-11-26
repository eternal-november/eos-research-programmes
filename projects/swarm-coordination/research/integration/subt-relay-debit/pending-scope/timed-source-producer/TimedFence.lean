import Lean

namespace TimedFence

def Fits (cap tx rx packet : Nat) : Prop :=
  tx + packet ≤ cap ∧ rx + packet ≤ cap

theorem qualified_partial_effect {c tx rx x tx' rx' : Nat}
    (h : Fits c tx rx x) (sender : tx' ≤ tx) (receiver : rx' ≤ rx) :
    Fits c tx' rx' x := by
  unfold Fits at *
  omega

theorem after_erasure_only_tx_blocks :
    ¬ Fits 5 5 2 2 ∧ Fits 5 2 2 2 := by unfold Fits; decide

theorem after_success_both_aliases_block :
    ¬ Fits 5 5 2 2 ∧ ¬ Fits 5 2 5 2 := by unfold Fits; decide

#print axioms qualified_partial_effect
#print axioms after_erasure_only_tx_blocks
#print axioms after_success_both_aliases_block

end TimedFence
