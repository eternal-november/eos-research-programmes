import Mathlib

namespace DepartureClock

inductive Cmd where | idle | turnLeft | turnRight | forward
  deriving DecidableEq

-- The departure consumer only recognizes the immediately adjacent east
-- exit. Clearance at other locations is not this grant.
def first (c : Cmd) : Bool × Bool :=
  match c with
  | .turnRight => (true,false)
  | _ => (false,false)

def atExitAfter (s : Bool × Bool) (c : Cmd) : Bool :=
  s.2 || (s.1 && (c == .forward))

theorem one_command_cannot_clear (c : Cmd) : (first c).2 = false := by
  cases c <;> rfl

theorem two_commands_can_clear : atExitAfter (first .turnRight) .forward = true := by
  decide

theorem long_clock_cut (skew : ℕ) :
    8 < 2*(3+2)-skew ↔ skew < 2 := by omega

theorem no_shortcut_at_equality (skew : ℕ) :
    ¬ 8 < 2*(3+1)-skew := by omega

#print axioms one_command_cannot_clear
#print axioms two_commands_can_clear
#print axioms long_clock_cut
#print axioms no_shortcut_at_equality
end DepartureClock
