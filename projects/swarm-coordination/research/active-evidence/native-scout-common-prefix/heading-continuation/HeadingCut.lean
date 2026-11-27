import Mathlib
namespace HeadingCut

inductive Mode where
  | stay | cross | withdraw
  deriving DecidableEq

-- Boolean true means the occupied bay is left at the initial crop.
def reads (side : Bool) (m : Mode) : Bool × Bool :=
  (side, m != Mode.stay)

def final (side : Bool) : Mode → Bool
  | .cross => !side
  | _ => side

def predict (o : Bool × Bool) : Bool :=
  if o.2 then !o.1 else o.1

theorem qualified (side : Bool) (m : Mode) (h : m ≠ .withdraw) :
    predict (reads side m) = final side m := by
  cases m <;> simp_all [reads, final, predict]

theorem same_read_opposite_bay (side : Bool) :
    reads side .cross = reads side .withdraw ∧
    final side .cross ≠ final side .withdraw := by
  cases side <;> decide

theorem no_blind_cert (side : Bool) (policy : Bool × Bool → Bool) :
    ¬(policy (reads side .cross) = final side .cross ∧
      policy (reads side .withdraw) = final side .withdraw) := by
  rintro ⟨a,b⟩
  obtain ⟨eq,no⟩ := same_read_opposite_bay side
  rw [eq] at a
  exact no (a.symm.trans b)

#print axioms qualified
#print axioms same_read_opposite_bay
#print axioms no_blind_cert
end HeadingCut
