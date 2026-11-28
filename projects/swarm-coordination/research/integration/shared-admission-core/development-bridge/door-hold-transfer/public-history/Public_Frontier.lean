import Mathlib
namespace PublicFrontier

-- Positions relative to OPEN in 1/512; velocities in 1/64.
def step (x v : Int) (close : Bool) : Int × Int :=
  let err := (if close then -512 else 0) - x
  let err := if err.natAbs < 4 then 0 else err
  let s : Int := if err < 0 then -1 else 1
  let e := s * err
  let z := s * v
  let next := if z > 0 ∧ e > 0 ∧ z*z ≥ 2*e then z-1 else min e (min 16 (1+z))
  (x+s*next,s*next)

def pos (hi : Bool) (close : Bool) (expiry : Nat) : Nat → Int × Int
  | 0 => (0,if hi then -5 else -2)
  | t+1 =>
    let (x,v) := pos hi close expiry t
    step x v (close && decide (1 ≤ t ∧ expiry ≤ t))

def openAt (hi close : Bool) (expiry t : Nat) : Bool :=
  decide ((pos hi close expiry t).1 > -8)

def crosses (hi close : Bool) (expiry t : Nat) : Bool :=
  (List.range 5).all (fun d => openAt hi close expiry (t+d))

theorem unheld_full_information_obstruction :
    (List.range 7).all (fun t => !crosses true false 0 t && !crosses false true 0 t)
    = true := by decide

theorem unheld_delayed_success :
    crosses true false 0 7 = true ∧ crosses false false 0 7 = true := by decide

theorem indistinguishable_prefix :
    (List.range 3).all (fun t => openAt true false 0 t && openAt false true 0 t) = true ∧
    crosses false true 0 7 = false := by decide

theorem first_loss_discriminates :
    openAt true true 0 1 = true ∧ openAt true true 0 2 = false ∧
    openAt true false 0 2 = true ∧ openAt true false 0 3 = false ∧
    openAt false true 0 3 = true := by decide

theorem delayed_phase_with_hold :
    crosses false true 4 3 = true ∧ crosses false true 5 4 = true := by decide


-- A mandatory longer hold can coarsen a fixed early public report.
-- If the intervention is optional, retaining the zero-hold plan
-- avoids this policy-set regression.
theorem hold_erases_public_distinction :
    (List.range 4).all (fun t =>
      (openAt true true 2 t == openAt true false 2 t) &&
      (openAt false true 2 t == openAt false false 2 t)) = true ∧
    crosses true true 2 7 = false ∧
    crosses false true 2 7 = false ∧
    crosses true false 2 7 = true ∧
    crosses false false 2 7 = true := by decide

end PublicFrontier
