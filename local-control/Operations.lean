import Std

/-! Selected exact-discrete reconstruction lemmas. The all-history physical
attempt proof and its undischarged suppliers are in OPERATIONS.md. This file
does not mechanize a global repair scheduler, processor, or recurring theorem. -/
namespace ByzantineLocalOperations

def deadzone (threshold force : Int) : Int :=
  if threshold < force then force - threshold
  else if force < -threshold then force + threshold else 0

def clip (limit value : Int) : Int := max 0 (min limit value)

def stroke (limit threshold speed position force : Int) : Int :=
  clip limit (position + max (-speed) (min speed (deadzone threshold force)))

theorem deadzone_holds (threshold force : Int)
    (hlo : -threshold ≤ force) (hhi : force ≤ threshold) :
    deadzone threshold force = 0 := by
  unfold deadzone
  split <;> (try split) <;> omega

theorem stroke_retention (limit threshold speed position force : Int)
    (hp : 0 ≤ position) (hq : position ≤ limit) (hs : 0 ≤ speed)
    (hlo : -threshold ≤ force) (hhi : force ≤ threshold) :
    stroke limit threshold speed position force = position := by
  rw [stroke, deadzone_holds threshold force hlo hhi]
  unfold clip
  omega

theorem positive_motion_needs_nominal_effort (nominal hostile threshold : Int)
    (hhostile : hostile ≤ threshold)
    (hmotion : 0 < deadzone threshold (nominal + hostile)) : 0 < nominal := by
  unfold deadzone at hmotion
  split at hmotion
  · omega
  · split at hmotion <;> omega

theorem stroke_progress (limit threshold speed position force margin : Int)
    (hm : 0 < margin) (hs : margin ≤ speed)
    (hf : threshold + margin ≤ force) :
    min limit (position + margin) ≤ stroke limit threshold speed position force := by
  unfold stroke deadzone clip
  split <;> omega

theorem unit_progress_after (position : Nat → Nat) (limit : Nat)
    (hstep : ∀ t, min limit (position t + 1) ≤ position (t + 1)) :
    ∀ t, min limit (position 0 + t) ≤ position t := by
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
    have ht := hstep t
    omega

theorem stroke_reaches (position : Nat → Nat) (limit : Nat)
    (hstep : ∀ t, min limit (position t + 1) ≤ position (t + 1)) :
    limit ≤ position limit := by
  have h := unit_progress_after position limit hstep limit
  omega

theorem constant_storage {Image : Type} (memory : Nat → Image)
    (hstep : ∀ t, memory (t + 1) = memory t) :
    ∀ t, memory t = memory 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact (hstep t).trans ih

theorem sequential_reads_one_image {Address Cell : Type}
    (memory : Nat → Address → Cell) (sample : Address → Nat)
    (hstep : ∀ t, memory (t + 1) = memory t) :
    (fun a => memory (sample a) a) = memory 0 := by
  funext a
  rw [constant_storage memory hstep (sample a)]

theorem inspected_start {Image : Type} (readImage startImage intended : Image)
    (hread : readImage = intended) (hcontinuity : startImage = readImage) :
    startImage = intended := hcontinuity.trans hread

theorem permutation_does_not_preserve_slot_binding :
    ∃ (before after : Bool → Bool), before false = false ∧ after false ≠ false := by
  exact ⟨id, not, rfl, by decide⟩

theorem drain_before_unlock (entry delay response oldArrival clearArrival unlock : Int)
    (hd : 0 ≤ delay) (hj : 0 ≤ response)
    (hold : oldArrival ≤ entry + delay)
    (hclear : clearArrival ≤ entry + 2 * delay + response)
    (hwait : entry + 2 * delay + response < unlock) :
    oldArrival < unlock ∧ clearArrival < unlock := by omega

theorem scans_before_power (frozen firstMotion lastScan power latency : Int)
    (hfirst : frozen ≤ firstMotion)
    (hscan : lastScan ≤ frozen + latency)
    (hstroke : firstMotion + latency ≤ power) : lastScan ≤ power := by omega

theorem permission_through_latency (actual upper growth safe : Int)
    (hupper : actual ≤ upper + growth) (hguard : upper + growth ≤ safe) :
    actual ≤ safe := by omega

theorem image_equality_does_not_certify_cpu :
    ∃ (image : Bool) (ordinary latentFault : Bool → Bool),
      image = false ∧ ordinary image ≠ latentFault image := by
  exact ⟨false, id, not, rfl, by decide⟩

#print axioms deadzone_holds
#print axioms stroke_retention
#print axioms positive_motion_needs_nominal_effort
#print axioms stroke_progress
#print axioms unit_progress_after
#print axioms stroke_reaches
#print axioms constant_storage
#print axioms sequential_reads_one_image
#print axioms inspected_start
#print axioms permutation_does_not_preserve_slot_binding
#print axioms drain_before_unlock
#print axioms scans_before_power
#print axioms permission_through_latency
#print axioms image_equality_does_not_certify_cpu
end ByzantineLocalOperations
