import Std

/-! Extraction of a strictly long interval from a finite on-run partition.
The duration laws are stated minimally so that physical real times need not
be placed on a hardware-wide grid. The runnable application uses rationals. -/
namespace QuietWindow

structure Scale (D : Type) where
  zero : D
  add : D → D → D
  le : D → D → Prop
  refl : ∀ x, le x x
  mono : ∀ {x y u v}, le x y → le u v → le (add x u) (add y v)
  compare : ∀ x y, Decidable (le x y)

structure Gap (D Key : Type) where
  key : Key
  width : D
  deriving Repr

variable {D Key : Type}

def total (m : Scale D) : List (Gap D Key) → D
  | [] => m.zero
  | a :: rest => m.add a.width (total m rest)

def repeatBound (m : Scale D) (q : D) : Nat → D
  | 0 => m.zero
  | n+1 => m.add q (repeatBound m q n)

structure Long (m : Scale D) (q : D) (xs : List (Gap D Key)) where
  gap : Gap D Key
  occurs : gap ∈ xs
  wide : ¬m.le gap.width q

/-- The selector returns an actual gap, or a checked upper bound on the sum. -/
def scan (m : Scale D) (q : D) (xs : List (Gap D Key)) :
    Sum (Long m q xs) (PLift (m.le (total m xs) (repeatBound m q xs.length))) :=
  match xs with
  | [] => .inr ⟨m.refl _⟩
  | a :: rest =>
    match m.compare a.width q with
    | .isFalse big => .inl ⟨a, List.Mem.head _, big⟩
    | .isTrue small =>
      match scan m q rest with
      | .inl later => .inl ⟨later.gap, List.Mem.tail a later.occurs, later.wide⟩
      | .inr bound => .inr ⟨m.mono small bound.down⟩

/-- For nonnegative physical durations the source derives this strict premise
from occupied work and the actual event-count envelope on the same interval. -/
def locate (m : Scale D) (q : D) (xs : List (Gap D Key))
    (room : ¬m.le (total m xs) (repeatBound m q xs.length)) : Long m q xs :=
  match scan m q xs with
  | .inl actual => actual
  | .inr bounded => False.elim (room bounded.down)

/-- A retrospective witness applies only to an operation already running
under the originally fixed policy, without giving its actor the selector. -/
def receipt (m : Scale D) (q : D) (xs : List (Gap D Key))
    (Evidence : Gap D Key → Type)
    (onRun : (g : Gap D Key) → g ∈ xs → (¬m.le g.width q) → Evidence g)
    (room : ¬m.le (total m xs) (repeatBound m q xs.length)) :
    (g : Gap D Key) × (PLift (g ∈ xs) × Evidence g) :=
  let chosen := locate m q xs room
  ⟨chosen.gap, ⟨chosen.occurs⟩, onRun chosen.gap chosen.occurs chosen.wide⟩

def natScale : Scale Nat := ⟨0, Nat.add, LE.le, Nat.le_refl,
  fun h k => Nat.add_le_add h k, fun x y => inferInstanceAs (Decidable (x ≤ y))⟩

def sample : List (Gap Nat Nat) := [⟨0,2⟩, ⟨7,8⟩, ⟨16,1⟩]

#eval match scan natScale 3 sample with
  | .inl result => some result.gap.key
  | .inr _ => none

#print axioms scan
#print axioms locate
#print axioms receipt

end QuietWindow
