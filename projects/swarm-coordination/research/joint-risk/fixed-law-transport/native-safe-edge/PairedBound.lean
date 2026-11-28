import Lean.Elab.Tactic.Omega
namespace PairedRisk
def ab (z : Int) := if 0 ≤ z then z else -z
theorem suffixLower (q Q s t : Int) :
    ab (Q-q-(t-s)) + ab (t-s) ≥ ab (Q-q) := by
  unfold ab
  split <;> split <;> split <;> omega

theorem suffixWitness (q Q t : Int)
    (hq : 0 ≤ q) (ht : 0 ≤ t) (hT : t ≤ Q) :
    ∃ s, 0 ≤ s ∧ s ≤ q ∧
      ab (Q-q-(t-s)) + ab (t-s) = ab (Q-q) := by
  refine ⟨min q t, ?_, ?_, ?_⟩
  · omega
  · omega
  · unfold ab
    split <;> split <;> split <;> omega

theorem gapInterval (N P Q d e δ t : Int) :
    (0 ≤ t ∧ P+Q-N ≤ t ∧ t ≤ P ∧ t ≤ Q ∧
     ab e ≤ δ ∧ ab (d-t) ≤ δ ∧ ab (t-d-e) ≤ δ) ↔
    (ab e ≤ δ ∧ max (max 0 (P+Q-N)) (max (d-δ) (d+e-δ)) ≤ t ∧
      t ≤ min (min P Q) (min (d+δ) (d+e+δ))) := by
  unfold ab
  split <;> split <;> split <;> omega
end PairedRisk
