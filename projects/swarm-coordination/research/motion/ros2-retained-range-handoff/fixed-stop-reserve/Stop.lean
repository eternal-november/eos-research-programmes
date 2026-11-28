import Lean.Elab.Tactic.Omega
namespace FixedStop
theorem minBrakeStep (p u r : Int) (hn : 0 ≤ u) (hr : p-r ≤ u) :
    max 0 (p-r) ≤ u := by omega
theorem reserveDecreasesExactly (b p r t b' : Int)
    (hDef : b = max 0 (p-r) + t) (hBudget : b ≤ b')
    : t ≤ b' - max 0 (p-r) := by omega
theorem unsafeFirst (room u rem : Int)
    (pointwise : u ≤ room) (later : room < u+rem) :
    (0 ≤ room-u) ∧ (room-u < rem) := by omega
end FixedStop
