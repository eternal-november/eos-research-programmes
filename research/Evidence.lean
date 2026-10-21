import Std

/-! Fault-labelled inference and witnessed control. The analytic timed theorem is
in EVIDENCE.md; no real-analysis theorem is claimed by this Std-only module. -/
namespace ByzantineEvidence

def Hypothesis {I X : Type} (F : (I → Prop) → Prop)
    (constraint : I → X → Prop) (x : X) (B : I → Prop) : Prop :=
  F B ∧ ∀ s, ¬ B s → constraint s x

def Envelope {I X : Type} (F : (I → Prop) → Prop)
    (constraint : I → X → Prop) (x : X) : Prop :=
  ∃ B, Hypothesis F constraint x B

theorem actual_hypothesis {I X : Type} (F : (I → Prop) → Prop)
    (constraint : I → X → Prop) (x : X) (B : I → Prop)
    (admitted : F B) (sound : ∀ s, ¬ B s → constraint s x) :
    Hypothesis F constraint x B := ⟨admitted, sound⟩

theorem envelope_coverage {I X : Type} (F : (I → Prop) → Prop)
    (constraint : I → X → Prop) (x : X) (B : I → Prop)
    (actual : Hypothesis F constraint x B) : Envelope F constraint x := ⟨B, actual⟩

/- The relation R can be a distance bound or any decision-consumed relation.
The same F is used for the actual and alternative fault hypotheses. -/
theorem shared_source_bound {I X : Type} (F : (I → Prop) → Prop)
    (constraint : I → X → Prop) (R : X → X → Prop)
    (overlap : ∀ B C, F B → F C → ∃ s, ¬ B s ∧ ¬ C s)
    (diameter : ∀ s x z, constraint s x → constraint s z → R x z)
    (x z : X) (B : I → Prop) (actual : Hypothesis F constraint x B)
    (alternative : Envelope F constraint z) : R x z := by
  obtain ⟨C, hC, hz⟩ := alternative
  obtain ⟨s, hB, hC'⟩ := overlap B C actual.1 hC
  exact diameter s x z (actual.2 s hB) (hz s hC')

/- Missing/faulty sources may supply unrestricted constraints. Only the shared
ACTUALLY honest source needs the decision bound. -/
theorem shared_honest_source_bound {I X : Type} (F : (I → Prop) → Prop)
    (constraint : I → X → Prop) (R : X → X → Prop)
    (overlap : ∀ B C, F B → F C → ∃ s, ¬ B s ∧ ¬ C s)
    (x z : X) (B : I → Prop) (actual : Hypothesis F constraint x B)
    (diameter : ∀ s, ¬ B s → ∀ z, constraint s x → constraint s z → R x z)
    (alternative : Envelope F constraint z) : R x z := by
  obtain ⟨C, hC, hz⟩ := alternative
  obtain ⟨s, hB, hC'⟩ := overlap B C actual.1 hC
  exact diameter s hB z (actual.2 s hB) (hz s hC')

theorem added_evidence_refines {I X : Type} (F : (I → Prop) → Prop)
    (old fresh : I → X → Prop)
    (stronger : ∀ s x, fresh s x → old s x) (x : X) (B : I → Prop) :
    Hypothesis F fresh x B → Hypothesis F old x B := by
  rintro ⟨hF, h⟩
  exact ⟨hF, fun s hs => stronger s x (h s hs)⟩

def Robust {I X A : Type} (H : X → (I → Prop) → Prop)
    (legal : X → (I → Prop) → A → Prop) (a : A) : Prop :=
  ∀ x B, H x B → legal x B a

theorem robust_decision_sound {I X A : Type} (H : X → (I → Prop) → Prop)
    (legal : X → (I → Prop) → A → Prop) (x : X) (B : I → Prop) (a : A)
    (actual : H x B) (certificate : Robust H legal a) : legal x B a := certificate x B actual

theorem evidence_expands_safe_actions {I X A : Type}
    (old fresh : X → (I → Prop) → Prop) (legal : X → (I → Prop) → A → Prop)
    (refines : ∀ x B, fresh x B → old x B) (a : A) :
    Robust old legal a → Robust fresh legal a := by
  intro h x B hx
  exact h x B (refines x B hx)

/- A single honest permission suffices for effect safety; live support and interval
intersection are separate requirements in the operational/analytic construction. -/
theorem supported_action_sound {I A : Type} (B Q : I → Prop)
    (endorse : I → A → Prop) (safe : A → Prop) (a : A)
    (hit : ∃ i, Q i ∧ ¬ B i)
    (shares : ∀ i, Q i → endorse i a)
    (honest : ∀ i, ¬ B i → endorse i a → safe a) : safe a := by
  obtain ⟨i, hi, hgood⟩ := hit
  exact honest i hgood (shares i hi)

/- World/fault projection can erase the only input to a valid intervention. -/
theorem state_projection_loses_intervention :
    (∀ b : Bool, ∃ a : Bool, a = b) ∧
    ¬ (∃ f : Unit → Bool, ∀ b : Bool, f () = b) := by
  constructor
  · intro b; exact ⟨b, rfl⟩
  · rintro ⟨f, h⟩
    have hf := h false
    have ht := h true
    cases hf.symm.trans ht

inductive Scene where
  | lowOffset | highZero | corruptLow
  deriving DecidableEq, Repr

def target : Scene → Bool
  | .lowOffset => false | .highZero => true | .corruptLow => false
def pose : Scene → Bool
  | .lowOffset => true | .highZero => false | .corruptLow => false
def registered (_ : Scene) : Bool := true
def reported (_ : Scene) : Bool := true
def calibrated : Scene → Bool
  | .corruptLow => false | _ => true
def safeAction (s : Scene) (inject : Bool) : Prop := inject = !(target s)
def calibratedScenes (s : Scene) : Prop := s ≠ .corruptLow

def sceneNext (s : Scene) (inject : Bool) : Int :=
  (if target s then 1 else 0) + 2 * (if inject then 1 else 0) - 1

theorem scene_action_effect_equivalence (s : Scene) (inject : Bool) :
    safeAction s inject ↔ (0 ≤ sceneNext s inject ∧ sceneNext s inject ≤ 1) := by
  cases s <;> cases inject <;> simp [safeAction, target, sceneNext]

theorem calibrated_measurement_law (s : Scene) (h : calibratedScenes s) :
    registered s = Bool.xor (target s) (pose s) := by
  cases s <;> simp_all [calibratedScenes, registered, target, pose, Bool.xor]

theorem report_alone_no_safe_policy :
    ¬ ∃ f : Bool → Bool, ∀ s, calibratedScenes s → safeAction s (f (reported s)) := by
  rintro ⟨f, h⟩
  have hl := h .lowOffset (by simp [calibratedScenes])
  have hh := h .highZero (by simp [calibratedScenes])
  simp [safeAction, reported, target] at hl hh
  rw [hl] at hh
  contradiction

theorem pose_witness_supplies_safe_policy (s : Scene) (h : calibratedScenes s) :
    safeAction s (pose s) := by
  cases s <;> simp_all [calibratedScenes, safeAction, target, pose]

theorem pose_and_register_do_not_establish_calibration :
    pose .highZero = pose .corruptLow ∧
    registered .highZero = registered .corruptLow ∧
    reported .highZero = reported .corruptLow ∧
    target .highZero ≠ target .corruptLow := by decide

theorem pose_policy_fails_without_calibration : ¬ safeAction .corruptLow (pose .corruptLow) := by simp [safeAction, pose, target]

structure PhysicalRecord where
  scene : Bool
  internal : Bool
  message : Bool
  deriving DecidableEq

def externalObservation (r : PhysicalRecord) : Bool × Bool := (r.scene, r.message)

theorem scene_and_message_do_not_identify_register :
    ∃ a b : PhysicalRecord,
      externalObservation a = externalObservation b ∧ a.internal ≠ b.internal := by
  exact ⟨⟨false, false, true⟩, ⟨false, true, true⟩, rfl, by decide⟩

/- The exact integer affine certificate is a mechanized algebraic interface, not
a mechanization of the continuous tube theorem or a restriction of its carrier. -/
def IntervalSafe (lo hi z : Int) : Prop := lo ≤ z ∧ z ≤ hi
def EndpointCertificate (lo hi L U d r c u : Int) : Prop :=
  0 ≤ u ∧ u ≤ c ∧ lo ≤ L + u - d - r ∧ U + u - d + r ≤ hi

theorem endpoint_certificate_exact (lo hi L U d r c u : Int) :
    EndpointCertificate lo hi L U d r c u ↔
      0 ≤ u ∧ u ≤ c ∧ lo - L + d + r ≤ u ∧ u ≤ hi - U + d - r := by
  unfold EndpointCertificate
  omega

theorem endpoint_certificate_sound (lo hi L U d r c u x w : Int)
    (hx : L ≤ x ∧ x ≤ U) (hw : -r ≤ w ∧ w ≤ r)
    (cert : EndpointCertificate lo hi L U d r c u) :
    IntervalSafe lo hi (x + u - d + w) := by
  unfold EndpointCertificate IntervalSafe at *
  omega

theorem exclusion_record_not_effect :
    IntervalSafe 0 4 (0 + 1 - 1 + 0) ∧ ¬ IntervalSafe 0 4 (0 + 1 - 1 + (-1)) := by simp [IntervalSafe]

#print axioms actual_hypothesis
#print axioms envelope_coverage
#print axioms shared_source_bound
#print axioms shared_honest_source_bound
#print axioms added_evidence_refines
#print axioms robust_decision_sound
#print axioms evidence_expands_safe_actions
#print axioms supported_action_sound
#print axioms state_projection_loses_intervention
#print axioms calibrated_measurement_law
#print axioms scene_action_effect_equivalence
#print axioms report_alone_no_safe_policy
#print axioms pose_witness_supplies_safe_policy
#print axioms pose_and_register_do_not_establish_calibration
#print axioms pose_policy_fails_without_calibration
#print axioms scene_and_message_do_not_identify_register
#print axioms endpoint_certificate_exact
#print axioms endpoint_certificate_sound
#print axioms exclusion_record_not_effect
end ByzantineEvidence
