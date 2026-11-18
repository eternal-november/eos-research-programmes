import Std

/-! Raw history bookkeeping only. No statement here says that an aged-out
domain has actually recovered. That is a source/algorithm obligation. -/
namespace LocalReturn

structure Episode where
  domain : Nat
  acquire : Int
  release : Int

def HeldBefore (episodes : List Episode) (d : Nat) (t : Int) : Prop :=
  ∃ e ∈ episodes, e.domain = d ∧ e.acquire < t ∧ t ≤ e.release

def Acquired (episodes : List Episode) (d : Nat) (a b : Int) : Prop :=
  ∃ e ∈ episodes, e.domain = d ∧ a ≤ e.acquire ∧ e.acquire ≤ b

def Cover (persistent : Nat → Prop) (episodes : List Episode)
    (d : Nat) (a b : Int) : Prop :=
  persistent d ∨ HeldBefore episodes d a ∨ Acquired episodes d a b

theorem enlarge_cover (persistent : Nat → Prop) (episodes : List Episode)
    (d : Nat) (a b u finish : Int)
    (left : a ≤ b) (ordered : b ≤ u) (right : u ≤ finish)
    (covered : Cover persistent episodes d b u) :
    Cover persistent episodes d a finish := by
  rcases covered with hp | hh | ha
  · exact Or.inl hp
  · rcases hh with ⟨e, he, hd, hs, hr⟩
    by_cases before : e.acquire < a
    · exact Or.inr (Or.inl ⟨e, he, hd, before, by omega⟩)
    · exact Or.inr (Or.inr ⟨e, he, hd, by omega, by omega⟩)
  · rcases ha with ⟨e, he, hd, hs, hr⟩
    exact Or.inr (Or.inr ⟨e, he, hd, by omega, by omega⟩)

theorem rolling_window_cover (persistent : Nat → Prop) (episodes : List Episode)
    (d : Nat) (s u W H : Int) (hH : 0 ≤ H)
    (start : s ≤ u) (finish : u ≤ s+W)
    (covered : Cover persistent episodes d (u-H) u) :
    Cover persistent episodes d (s-H) (s+W) := by
  exact enlarge_cover persistent episodes d (s-H) (u-H) u (s+W)
    (by omega) (by omega) finish covered

theorem clipped_window_cover (persistent : Nat → Prop) (episodes : List Episode)
    (d : Nat) (s u W H : Int) (hs : 0 ≤ s) (hH : 0 ≤ H)
    (start : s ≤ u) (finish : u ≤ s+W)
    (covered : Cover persistent episodes d (max 0 (u-H)) u) :
    Cover persistent episodes d (max 0 (s-H)) (s+W) := by
  apply enlarge_cover persistent episodes d (max 0 (s-H)) (max 0 (u-H)) u (s+W)
  · omega
  · omega
  · exact finish
  · exact covered

theorem initial_debt_window (s u H : Int) (start : s ≤ u) (debt : u < H) :
    s < H := by omega

theorem strict_return_slack (start elapsed deadline H : Int)
    (within : elapsed < H) (ends : deadline = start+elapsed) :
    deadline < start+H := by omega

#print axioms enlarge_cover
#print axioms rolling_window_cover
#print axioms clipped_window_cover
#print axioms initial_debt_window
#print axioms strict_return_slack

end LocalReturn
