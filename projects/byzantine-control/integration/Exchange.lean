import Std
namespace ByzantineExchange
def speed (x u e : Nat) : Nat := (5*x+10*u-10*e)/10
def heat (h x e : Nat) : Nat := (5*h+x*e)/10
theorem limited_speed {x u e : Nat} (hx : x ≤ 10) (hu : u ≤ 5) :
    speed x u e ≤ 10 := by unfold speed; omega
theorem normal_service {x e : Nat} (hx : 1 ≤ x) (he : e ≤ 3) :
    1 ≤ speed x 4 e := by unfold speed; omega
theorem bounded_heat {h x e : Nat} (hh : h ≤ 6) (hx : x ≤ 10) (he : e ≤ 3) :
    heat h x e ≤ 6 := by
  have hem : x*e ≤ 30 := by
    have := Nat.mul_le_mul hx he
    omega
  unfold heat
  omega
theorem limited_joint_step {x h u e : Nat}
    (hx : x ≤ 10) (hh : h ≤ 6) (hu : u ≤ 5) (he : e ≤ 3) :
    speed x u e ≤ 10 ∧ heat h x e ≤ 6 ∧
    (1 ≤ x → u = 4 → 1 ≤ speed x u e) := by
  refine ⟨limited_speed hx hu, bounded_heat hh hx he, ?_⟩
  intro hl hu4
  subst u
  exact normal_service hl he
theorem removal_witness :
    speed 4 6 0 = 8 ∧ speed 8 6 0 = 10 ∧ speed 10 6 0 = 11 ∧ ¬ (11 ≤ 10) := by decide
theorem limited_same_requests :
    speed 4 (min 6 5) 0 = 7 ∧ speed 7 (min 6 5) 0 = 8 ∧
    speed 8 (min 6 5) 0 = 9 ∧ speed 10 (min 6 5) 0 = 10 := by decide
end ByzantineExchange
#print axioms ByzantineExchange.limited_speed
#print axioms ByzantineExchange.normal_service
#print axioms ByzantineExchange.bounded_heat
#print axioms ByzantineExchange.limited_joint_step
#print axioms ByzantineExchange.removal_witness
#print axioms ByzantineExchange.limited_same_requests
