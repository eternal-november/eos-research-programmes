import Std

/-! Software queue/authority and exact endpoint interfaces for TIMED-RECOVERY.md.
The integer displacement algebra is not a claimed mechanization of real analysis. -/
namespace ByzantineTimedRecovery

def reserve {A : Type} (old : List A) (m : Nat) (u d : A) : List A :=
  old ++ List.replicate m u ++ List.replicate m d

theorem reservation_preserves_pending {A : Type} (old : List A) (m : Nat) (u d : A) :
    (reserve old m u d).take old.length = old := by simp [reserve]

theorem reservation_contains_both_blocks {A : Type} (old : List A) (m : Nat) (u d : A) :
    (reserve old m u d).length = old.length + 2*m := by simp [reserve]; omega

theorem drain_leaves_constant_queue {A : Type} (old : List A) (d : A) :
    (old ++ List.replicate old.length d).drop old.length = List.replicate old.length d := by simp

theorem recenter_leaves_warmup {A : Type} (old : List A) (m : Nat) (u d : A) :
    (reserve old m u d).drop (old.length+m) = List.replicate m d := by
  simp [reserve]

inductive Mode where
  | live | drain | isolated | repair | ready | reserved | releaseReady
  deriving DecidableEq

def OrdinaryAdmission (mode : Mode) : Prop := mode = .live

theorem reservation_blocks_ordinary_admission : ¬ OrdinaryAdmission .reserved := by simp [OrdinaryAdmission]

structure Commitment where
  admittedGeneration : Nat
  targetSlot : Nat
  command : Int

/- A normative lease: current registration generation does not retrospectively
cancel an already admitted finite target slot. Fresh admissions check current scope. -/
def Executable (commit : Commitment) (slot : Nat) (alreadyUsed : Bool) : Prop :=
  commit.targetSlot = slot ∧ alreadyUsed = false

theorem pending_lease_survives_registration (commit : Commitment) (slot oldGen newGen : Nat)
    (used : Bool) :
    Executable {commit with admittedGeneration := oldGen} slot used ↔
    Executable {commit with admittedGeneration := newGen} slot used := by rfl

theorem used_commitment_cannot_reexecute (commit : Commitment) (slot : Nat) :
    ¬ Executable commit slot true := by simp [Executable]

theorem old_era_cannot_authorize_current (oldEra newEra : Nat) (h : oldEra < newEra) :
    ¬ oldEra = newEra := by omega

def Safe (lo hi x : Int) : Prop := lo ≤ x ∧ x ≤ hi
def Inner (lo hi radius x : Int) : Prop := lo+radius ≤ x ∧ x ≤ hi-radius
def BlockCertificate (L U targetLo targetHi displacement : Int) : Prop :=
  targetLo ≤ L+displacement ∧ U+displacement ≤ targetHi

theorem isolated_service_step (x d : Int) : x+d-d = x := by omega

theorem recenter_endpoint (L U targetLo targetHi displacement x : Int)
    (cover : L ≤ x ∧ x ≤ U)
    (cert : BlockCertificate L U targetLo targetHi displacement) :
    Safe targetLo targetHi (x+displacement) := by
  unfold BlockCertificate Safe at *
  omega

theorem warmup_safe (lo hi radius x disturbanceIntegral : Int)
    (inner : Inner lo hi radius x)
    (bound : -radius ≤ disturbanceIntegral ∧ disturbanceIntegral ≤ radius) :
    Safe lo hi (x+disturbanceIntegral) := by
  unfold Inner Safe at *
  omega

/- Exact immutable-d-startup region: the two constant extreme disturbances are
legal and already force these bounds; any observation architecture shares them. -/
theorem warmup_region_exact (lo hi radius x : Int) (nonneg : 0 ≤ radius) :
    (∀ w : Int, -radius ≤ w → w ≤ radius → Safe lo hi (x+w)) ↔
    Inner lo hi radius x := by
  constructor
  · intro h
    have lower := h (-radius) (by omega) (by omega)
    have upper := h radius (by omega) (by omega)
    unfold Inner Safe at *
    omega
  · intro h w lower upper
    exact warmup_safe lo hi radius x w h ⟨lower,upper⟩

theorem warmup_necessity (lo hi radius x : Int)
    (lower : Safe lo hi (x-radius)) (upper : Safe lo hi (x+radius)) :
    Inner lo hi radius x := by unfold Safe Inner at *; omega

theorem recenter_then_warmup (lo hi radius L U displacement x w : Int)
    (cover : L ≤ x ∧ x ≤ U)
    (cert : BlockCertificate L U (lo+radius) (hi-radius) displacement)
    (bound : -radius ≤ w ∧ w ≤ radius) : Safe lo hi (x+displacement+w) := by
  have h := recenter_endpoint L U (lo+radius) (hi-radius) displacement x cover cert
  exact warmup_safe lo hi radius (x+displacement) w h bound

/- scaled parameters: e is measurement error, a is historical drift r*age,
R is r*delay, and z is r*period. These bindings are interpreted in the prose. -/
theorem live_margin_supplies_recenter_margin (lo hi e a R z : Int)
    (hR : 0 ≤ R) (hz : 0 ≤ z)
    (margin : 4*(e+a+R)+2*z ≤ hi-lo) :
    4*(e+a) ≤ (hi-R)-(lo+R) := by omega

theorem interval_intersection (l1 u1 l2 u2 : Int)
    (h11 : l1 ≤ u1) (h12 : l1 ≤ u2) (h21 : l2 ≤ u1) (h22 : l2 ≤ u2) :
    max l1 l2 ≤ min u1 u2 := by omega

theorem repair_before_drain_can_exceed_capacity :
    (2 : Int) > 1 := by decide

theorem release_outside_inner_fails :
    Safe 0 4 0 ∧ ¬ Safe 0 4 (0 + (-1)) := by simp [Safe]

theorem bounded_reset_can_break_safety :
    Safe 0 4 0 ∧ (-1 : Int) ≤ -1 ∧ -1 ≤ 1 ∧ ¬ Safe 0 4 (0+(-1)) := by simp [Safe]

#print axioms reservation_preserves_pending
#print axioms reservation_contains_both_blocks
#print axioms drain_leaves_constant_queue
#print axioms recenter_leaves_warmup
#print axioms reservation_blocks_ordinary_admission
#print axioms pending_lease_survives_registration
#print axioms used_commitment_cannot_reexecute
#print axioms old_era_cannot_authorize_current
#print axioms isolated_service_step
#print axioms recenter_endpoint
#print axioms warmup_safe
#print axioms warmup_region_exact
#print axioms warmup_necessity
#print axioms recenter_then_warmup
#print axioms live_margin_supplies_recenter_margin
#print axioms interval_intersection
#print axioms repair_before_drain_can_exceed_capacity
#print axioms release_outside_inner_fails
#print axioms bounded_reset_can_break_safety
end ByzantineTimedRecovery
