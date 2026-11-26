import Mathlib

theorem shifting_dissent_preserves_other (a b t : ℕ)
    (h1 : t ≤ a) (h2 : a+b ≤ 2*t) :
    a-(a-t) = t ∧ b+(a-t) ≤ t := by omega

def B3 := Bool × Bool × Bool

def hd (x y : B3) : ℕ :=
  (if x.1 == y.1 then 0 else 1) +
  (if x.2.1 == y.2.1 then 0 else 1) +
  (if x.2.2 == y.2.2 then 0 else 1)

theorem three_world_collision :
    hd (true,false,false) (false,false,false) ≤ 1 ∧
    hd (true,false,false) (true,true,false) ≤ 1 ∧
    hd (true,false,false) (true,false,true) ≤ 1 := by decide

theorem tetrahedron_no_center (x y z : Bool) :
    ¬(hd (x,y,z) (false,false,false) ≤ 1 ∧
      hd (x,y,z) (false,true,true) ≤ 1 ∧
      hd (x,y,z) (true,false,true) ≤ 1 ∧
      hd (x,y,z) (true,true,false) ≤ 1) := by
  cases x <;> cases y <;> cases z <;> decide

#print axioms shifting_dissent_preserves_other
#print axioms three_world_collision
#print axioms tetrahedron_no_center
