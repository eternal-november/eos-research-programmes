import Control

/-! Institution and recovery refinement of the integer benchmark. Physical root and
authentication assumptions remain operational obligations documented in INSTITUTION.md. -/
namespace ByzantineInstitution
open ByzantineControlResearch

def LawfulCertified (permit : Int → Prop) (m u : Int) : Prop := Certified m u ∧ permit u

def LawfulAccepted (permit : Int → Prop) (bad : Fin 3) (med : Fin 3 → Int) (u : Int) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ (i ≠ bad → LawfulCertified permit (med i) u) ∧
    (j ≠ bad → LawfulCertified permit (med j) u)

theorem lawful_gate_sound (permit : Int → Prop) (x u b : Int) (bad : Fin 3)
    (med : Fin 3 → Int) (hs : Safe x) (sound : ∀ i, i ≠ bad → Near x (med i))
    (h : LawfulAccepted permit bad med u) (hb : -1 ≤ b) (hb' : b ≤ 1) :
    Safe (x + u - 1 + b) ∧ permit u := by
  obtain ⟨i,j,hij,hi,hj⟩ := h
  by_cases hbad : i = bad
  · have hgood : j ≠ bad := by intro heq; exact hij (hbad.trans heq.symm)
    exact ⟨certified_step x (med j) u b hs (sound j hgood) (hj hgood).1 hb hb', (hj hgood).2⟩
  · exact ⟨certified_step x (med i) u b hs (sound i hbad) (hi hbad).1 hb hb', (hi hbad).2⟩

theorem lawful_gate_available (permit : Int → Prop) (x : Int) (bad : Fin 3)
    (med : Fin 3 → Int) (hs : Safe x) (sound : ∀ i, i ≠ bad → Near x (med i))
    (allowed : permit (common x)) : LawfulAccepted permit bad med (common x) := by
  obtain ⟨i,j,hij,hi,hj⟩ := two_honest bad
  exact ⟨i,j,hij,fun _ => ⟨common_certified x (med i) hs (sound i hi),allowed⟩,
    fun _ => ⟨common_certified x (med j) hs (sound j hj),allowed⟩⟩

def RobustRegion (lo hi d c r : Int) : Prop :=
  ∀ x, lo ≤ x → x ≤ hi → ∃ u, 0 ≤ u ∧ u ≤ c ∧
    ∀ b, -r ≤ b → b ≤ r → lo ≤ x + u - d + b ∧ x + u - d + b ≤ hi

theorem robust_region_iff (lo hi d c r : Int) (ordered : lo ≤ hi) (radius : 0 ≤ r) :
    RobustRegion lo hi d c r ↔ d + r ≤ c ∧ r ≤ d ∧ 2*r ≤ hi-lo := by
  constructor
  · intro h
    obtain ⟨u,hu,huc,hstep⟩ := h lo (by omega) ordered
    have hl := hstep (-r) (by omega) (by omega)
    have hh := hstep r (by omega) (by omega)
    obtain ⟨v,hv,hvc,vstep⟩ := h hi ordered (by omega)
    have vh := vstep r (by omega) (by omega)
    omega
  · rintro ⟨hc,hd,hw⟩ x hx hxh
    by_cases hneed : 0 ≤ lo-x+d+r
    · refine ⟨lo-x+d+r, hneed, by omega, ?_⟩
      intro b hb hb'; omega
    · refine ⟨0, by omega, by omega, ?_⟩
      intro b hb hb'; omega

theorem forbidden_unit_cap : ¬ ∃ u : Int, 0 ≤ u ∧ u ≤ 1 ∧ Safe (2+u-1+(-1)) := by
  simp only [Safe]; omega

inductive Mode where
  | live | isolated | repair | ready
  deriving DecidableEq, Repr

def capacity : Mode → Int | .repair => 1 | _ => 2
def radius : Mode → Int | .live => 1 | _ => 0

def NextMode : Mode → Mode → Prop
  | .live, .isolated => True
  | .isolated, .repair => True
  | .repair, .ready => True
  | .ready, .live => True
  | a,b => a = b

def ModeAction (mode : Mode) (bad : Fin 3) (med : Fin 3 → Int) (u : Int) : Prop :=
  match mode with
  | .live => Accepted bad med u
  | _ => u = 1

theorem mode_service_step (mode : Mode) (x u b : Int) (bad : Fin 3) (med : Fin 3 → Int)
    (hs : Safe x) (sound : ∀ i, i ≠ bad → Near x (med i))
    (action : ModeAction mode bad med u) (bounds : -radius mode ≤ b ∧ b ≤ radius mode) :
    0 ≤ u ∧ u ≤ capacity mode ∧ Safe (x+u-1+b) := by
  cases mode with
  | live =>
    have safe := gate_safe x u b bad med hs sound action bounds.1 bounds.2
    obtain ⟨i,j,hij,hi,hj⟩ := action
    have control : 0 ≤ u ∧ u ≤ 2 := by
      by_cases h : i = bad
      · have hjb : j ≠ bad := by intro h'; exact hij (h.trans h'.symm)
        exact ⟨(hj hjb).1,(hj hjb).2.1⟩
      · exact ⟨(hi h).1,(hi h).2.1⟩
    exact ⟨control.1,control.2,safe⟩
  | isolated => simp only [ModeAction] at action; simp only [radius] at bounds; simp only [capacity,Safe] at *; omega
  | repair => simp only [ModeAction] at action; simp only [radius] at bounds; simp only [capacity,Safe] at *; omega
  | ready => simp only [ModeAction] at action; simp only [radius] at bounds; simp only [capacity,Safe] at *; omega

theorem mode_action_exists (mode : Mode) (x : Int) (bad : Fin 3) (med : Fin 3 → Int)
    (hs : Safe x) (sound : ∀ i, i ≠ bad → Near x (med i)) :
    ∃ u, ModeAction mode bad med u := by
  cases mode with
  | live => exact ⟨common x, gate_available x bad med hs sound⟩
  | isolated => exact ⟨1,rfl⟩
  | repair => exact ⟨1,rfl⟩
  | ready => exact ⟨1,rfl⟩

/- bad is configuration-relative; the operational adapter must obtain each bad t
from one fixed global B, never choose or reset the coalition independently. -/
theorem recovery_invariant (x u b : Nat → Int) (mode : Nat → Mode)
    (bad : Nat → Fin 3) (med : Nat → Fin 3 → Int) (init : Safe (x 0))
    (sound : ∀ t i, i ≠ bad t → Near (x t) (med t i))
    (action : ∀ t, ModeAction (mode t) (bad t) (med t) (u t))
    (bounds : ∀ t, -radius (mode t) ≤ b t ∧ b t ≤ radius (mode t))
    (step : ∀ t, x (t+1) = x t + u t - 1 + b t) : ∀ t, Safe (x t) := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih =>
    rw [step t]
    exact (mode_service_step (mode t) (x t) (u t) (b t) (bad t) (med t) ih
      (sound t) (action t) (bounds t)).2.2

def cumulative (delivered : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => cumulative delivered n + delivered n

theorem recurring_unit_service (delivered : Nat → Nat) (one : ∀ t, delivered t = 1) :
    ∀ t, cumulative delivered t = t := by
  intro t; induction t with
  | zero => rfl
  | succ t ih => simp [cumulative, one, ih]

inductive Status where | active | suspended | repairing | ready
  deriving DecidableEq, Repr
inductive Order where | suspend | isolate | beginRepair | finishRepair | reinstate | grantTwo
  deriving DecidableEq, Repr
structure InstitutionalState where
  status : Status
  normCap : Nat
  generation : Nat
  deriving DecidableEq, Repr

def recognizedUpdate (s : InstitutionalState) : Order → InstitutionalState
  | .suspend => {s with status := .suspended}
  | .isolate => s
  | .beginRepair => {s with status := .repairing}
  | .finishRepair => {s with status := .ready}
  | .reinstate => {s with status := .active, generation := s.generation+1}
  | .grantTwo => {s with normCap := 2}

def permitted (s : InstitutionalState) (mode : Mode) (clean consent : Bool) : Order → Prop
  | .suspend => s.status = .active
  | .isolate => s.status = .suspended ∧ mode = .live
  | .beginRepair => s.status = .suspended ∧ mode = .isolated
  | .finishRepair => s.status = .repairing ∧ mode = .repair ∧ clean = true
  | .reinstate => s.status = .ready ∧ mode = .ready ∧ clean = true
  | .grantTwo => consent = true

/- Power is a constitutive rule, permission a conduct rule. Credential validity and
the recognized office are intentionally separate inputs to the rule of power. -/
def HasPower (credential office : Bool) : Prop := credential = true ∧ office = true
def ValidUpdate (credential office : Bool) (s s' : InstitutionalState) (o : Order) : Prop :=
  HasPower credential office ∧ s' = recognizedUpdate s o

theorem power_without_permission :
    ∃ s s', ValidUpdate true true s s' .grantTwo ∧ ¬ permitted s .live false false .grantTwo := by
  exact ⟨⟨.active,1,0⟩,⟨.active,2,0⟩,⟨⟨rfl,rfl⟩,rfl⟩,by simp [permitted]⟩

theorem credential_without_office : ¬ HasPower true false := by simp [HasPower]

theorem suspension_does_not_change_mode (s : InstitutionalState) (m : Mode) :
    (recognizedUpdate s .suspend, m).2 = m := rfl

def breachMonitor (failure : Nat → Prop) : Nat → Prop
  | 0 => False
  | n+1 => breachMonitor failure n ∨ failure n

theorem breach_monitor_exact (failure : Nat → Prop) :
    ∀ n, breachMonitor failure n ↔ ∃ t, t < n ∧ failure t := by
  intro n; induction n with
  | zero => simp [breachMonitor]
  | succ n ih =>
    simp only [breachMonitor, ih]
    constructor
    · rintro (⟨t,ht,hf⟩ | hf)
      · exact ⟨t,by omega,hf⟩
      · exact ⟨n,by omega,hf⟩
    · rintro ⟨t,ht,hf⟩
      by_cases heq : t = n
      · exact Or.inr (heq ▸ hf)
      · exact Or.inl ⟨t,by omega,hf⟩

structure Report where
  signer : Nat
  era : Nat
  epoch : Nat
  sample : Nat
  value : Int
  deriving DecidableEq

def SameSample (a b : Report) : Prop :=
  a.signer = b.signer ∧ a.era = b.era ∧ a.epoch = b.epoch ∧ a.sample = b.sample
def Equivocation (log : List Report) (a b : Report) : Prop :=
  a ∈ log ∧ b ∈ log ∧ SameSample a b ∧ a.value ≠ b.value
def ConsistentSigner (log : List Report) (i : Nat) : Prop :=
  ∀ a ∈ log, ∀ b ∈ log, a.signer = i → SameSample a b → a.value = b.value

theorem equivocation_sound (log : List Report) (a b : Report)
    (h : Equivocation log a b) : ¬ ConsistentSigner log a.signer := by
  intro hc
  exact h.2.2.2 (hc a h.1 b h.2.1 rfl h.2.2.1)

theorem equivocation_nonvacuous :
    let a : Report := ⟨2,0,0,0,4⟩
    let b : Report := ⟨2,0,0,0,6⟩
    Equivocation [a,b] a b := by simp [Equivocation,SameSample]

def ScopeMatches (installed era epoch : Nat) (artifactEra artifactEpoch : Nat) : Prop :=
  artifactEra = era ∧ artifactEra = installed ∧ artifactEpoch = epoch

theorem stale_era_rejected (installed era epoch ae artifactTime : Nat) (old : ae ≠ installed) :
    ¬ ScopeMatches installed era epoch ae artifactTime := by
  intro h; exact old h.2.1

theorem mixed_scopes_cannot_match (installed era epoch a b ta tb : Nat)
    (different : a ≠ b) :
    ¬ (ScopeMatches installed era epoch a ta ∧ ScopeMatches installed era epoch b tb) := by
  rintro ⟨ha,hb⟩; exact different (ha.2.1.trans hb.2.1.symm)

#print axioms lawful_gate_sound
#print axioms lawful_gate_available
#print axioms robust_region_iff
#print axioms forbidden_unit_cap
#print axioms mode_service_step
#print axioms mode_action_exists
#print axioms recovery_invariant
#print axioms recurring_unit_service
#print axioms power_without_permission
#print axioms credential_without_office
#print axioms suspension_does_not_change_mode
#print axioms breach_monitor_exact
#print axioms equivocation_sound
#print axioms equivocation_nonvacuous
#print axioms stale_era_rejected
#print axioms mixed_scopes_cannot_match
end ByzantineInstitution
