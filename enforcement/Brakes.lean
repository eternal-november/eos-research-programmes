import Std

/-! A discrete integer peer-brake instance. No trusted execution gate, real-valued
plant refinement, hardware calibration, or independent fault probabilities are assumed.
The companion BRAKE-PROOFS.md states the real-valued family and the adapter. -/
namespace ByzantineEnforcement

def Near (x y : Int) : Prop := x - 1 ≤ y ∧ y ≤ x + 1

def TwoSound (x a b c : Int) : Prop :=
  (Near x a ∧ Near x b) ∨ (Near x a ∧ Near x c) ∨ (Near x b ∧ Near x c)

def median (a b c : Int) : Int :=
  if a ≤ b then (if b ≤ c then b else if a ≤ c then c else a)
  else (if a ≤ c then a else if b ≤ c then c else b)

theorem median_sound (x a b c : Int) (h : TwoSound x a b c) :
    Near x (median a b c) := by
  unfold median TwoSound Near at *
  split <;> split <;> (try split) <;> omega

def command (y : Int) : Int := if 3 ≤ y then 1 else 0

theorem command_bounds (y : Int) : 0 ≤ command y ∧ command y ≤ 1 := by
  unfold command
  split <;> omega

theorem issued_on_justified (x a b c : Int) (h : TwoSound x a b c)
    (hon : command (median a b c) = 1) : 2 ≤ x := by
  have hm := median_sound x a b c h
  unfold command at hon
  unfold Near at hm
  split at hon <;> omega

theorem issued_off_sample (x a b c : Int) (h : TwoSound x a b c)
    (hoff : command (median a b c) = 0) : x ≤ 3 := by
  have hm := median_sound x a b c h
  unfold command at hoff
  unfold Near at hm
  split at hoff <;> omega

/- An intact planner has sound source redundancy independently of its actuator.
ActsOn additionally identifies the actual effect with that planner's issued command. -/
def ActsOn (sample engagement : Int) : Prop :=
  ∃ a b c : Int, TwoSound sample a b c ∧ engagement = command (median a b c)

def TwoAct (sample e0 e1 e2 : Int) : Prop :=
  (ActsOn sample e0 ∧ ActsOn sample e1) ∨
  (ActsOn sample e0 ∧ ActsOn sample e2) ∨
  (ActsOn sample e1 ∧ ActsOn sample e2)

def Bit (e : Int) : Prop := 0 ≤ e ∧ e ≤ 1

def SpeedSafe (x : Int) : Prop := 0 ≤ x ∧ x ≤ 10

def HeatSafe (h : Int) : Prop := 0 ≤ h ∧ h ≤ 6

def speed (x u e : Int) : Int := max 0 ((5*x + 10*u - 10*e) / 10)

def heat (h e x : Int) : Int := (5*h + e*x) / 10

theorem acts_off_sample (x e : Int) (ha : ActsOn x e) (hoff : e = 0) : x ≤ 3 := by
  obtain ⟨a,b,c,hs,he⟩ := ha
  exact issued_off_sample x a b c hs (he.symm.trans hoff)

theorem physical_dichotomy (x e0 e1 e2 : Int)
    (h0 : Bit e0) (h1 : Bit e1) (h2 : Bit e2)
    (ha : TwoAct x e0 e1 e2) :
    2 ≤ e0+e1+e2 ∨ x ≤ 3 := by
  by_cases hx : x ≤ 3
  · exact Or.inr hx
  · have hon : ∀ e, Bit e → ActsOn x e → e = 1 := by
      intro e he had
      have hn : e ≠ 0 := fun hz => hx (acts_off_sample x e had hz)
      unfold Bit at he
      omega
    unfold TwoAct at ha
    rcases ha with ha | ha | ha
    · have h01 := hon e0 h0 ha.1
      have h11 := hon e1 h1 ha.2
      unfold Bit at *
      exact Or.inl (by omega)
    · have h01 := hon e0 h0 ha.1
      have h21 := hon e2 h2 ha.2
      unfold Bit at *
      exact Or.inl (by omega)
    · have h11 := hon e1 h1 ha.1
      have h21 := hon e2 h2 ha.2
      unfold Bit at *
      exact Or.inl (by omega)

theorem sum_bounds (e0 e1 e2 : Int) (h0 : Bit e0) (h1 : Bit e1) (h2 : Bit e2) :
    0 ≤ e0+e1+e2 ∧ e0+e1+e2 ≤ 3 := by
  unfold Bit at *
  omega

theorem speed_nonnegative (x u e : Int) : 0 ≤ speed x u e := by
  unfold speed
  omega

theorem startup_speed (x u e : Int) (hx : 0 ≤ x ∧ x ≤ 4)
    (hu : 0 ≤ u ∧ u ≤ 6) (he : 0 ≤ e) : SpeedSafe (speed x u e) := by
  unfold speed SpeedSafe
  omega

theorem recent_low_envelope (x u e : Int) (hx : x ≤ 3)
    (hu : u ≤ 6) (he : 0 ≤ e) : speed x u e ≤ 7 := by
  unfold speed
  omega

theorem upper_engaged (x u e : Int) (hx : SpeedSafe x)
    (hu : u ≤ 6) (he : 2 ≤ e) : SpeedSafe (speed x u e) := by
  unfold speed SpeedSafe at *
  omega

theorem upper_recent (x u e : Int) (hx : x ≤ 7)
    (hu : u ≤ 6) (he : 0 ≤ e) : SpeedSafe (speed x u e) := by
  unfold speed SpeedSafe
  omega

theorem delayed_speed (old current oldU oldE u e0 e1 e2 : Int)
    (hcur : SpeedSafe current)
    (hprev : current = speed old oldU oldE)
    (holdU : oldU ≤ 6) (holdE : 0 ≤ oldE) (hu : u ≤ 6)
    (h0 : Bit e0) (h1 : Bit e1) (h2 : Bit e2)
    (ha : TwoAct old e0 e1 e2) :
    SpeedSafe (speed current u (e0+e1+e2)) := by
  rcases physical_dichotomy old e0 e1 e2 h0 h1 h2 ha with high | low
  · exact upper_engaged current u (e0+e1+e2) hcur hu high
  · have hc : current ≤ 7 := by
      rw [hprev]
      exact recent_low_envelope old oldU oldE low holdU holdE
    exact upper_recent current u (e0+e1+e2) hc hu (sum_bounds e0 e1 e2 h0 h1 h2).1

theorem service_step (x e : Int) (hx : 1 ≤ x) (he : e ≤ 3) :
    1 ≤ speed x 4 e := by
  unfold speed
  omega

theorem heat_step (h e x : Int) (hh : HeatSafe h) (hx : SpeedSafe x)
    (he : 0 ≤ e ∧ e ≤ 3) : HeatSafe (heat h e x) := by
  have cases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    unfold heat HeatSafe SpeedSafe at * <;> omega

/- All faults use the same actual stream. TwoAct is the consequence of at most one
faulty planner/actuator chain; source faults are handled inside each intact planner's
TwoSound premise. No cross-role stochastic independence is required. -/
theorem speed_run (x u e0 e1 e2 : Nat → Int)
    (init : 0 ≤ x 0 ∧ x 0 ≤ 4)
    (ub : ∀ t, 0 ≤ u t ∧ u t ≤ 6)
    (eb : ∀ t, Bit (e0 t) ∧ Bit (e1 t) ∧ Bit (e2 t))
    (localDelay : ∀ t, TwoAct (x t) (e0 (t+1)) (e1 (t+1)) (e2 (t+1)))
    (dyn : ∀ t, x (t+1) = speed (x t) (u t) (e0 t+e1 t+e2 t)) :
    ∀ t, SpeedSafe (x t) := by
  have paired : ∀ t, SpeedSafe (x t) ∧ SpeedSafe (x (t+1)) := by
    intro t
    induction t with
    | zero =>
      constructor
      · unfold SpeedSafe
        omega
      · rw [dyn 0]
        exact startup_speed (x 0) (u 0) (e0 0+e1 0+e2 0) init (ub 0)
          (sum_bounds _ _ _ (eb 0).1 (eb 0).2.1 (eb 0).2.2).1
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [dyn (t+1)]
      exact delayed_speed (x t) (x (t+1)) (u t) (e0 t+e1 t+e2 t)
        (u (t+1)) (e0 (t+1)) (e1 (t+1)) (e2 (t+1))
        ih.2 (dyn t) (ub t).2
        (sum_bounds _ _ _ (eb t).1 (eb t).2.1 (eb t).2.2).1
        (ub (t+1)).2 (eb (t+1)).1 (eb (t+1)).2.1 (eb (t+1)).2.2 (localDelay t)
  exact fun t => (paired t).1

theorem service_run (x u e0 e1 e2 : Nat → Int)
    (init : 1 ≤ x 0) (normal : ∀ t, u t = 4)
    (eb : ∀ t, Bit (e0 t) ∧ Bit (e1 t) ∧ Bit (e2 t))
    (dyn : ∀ t, x (t+1) = speed (x t) (u t) (e0 t+e1 t+e2 t)) :
    ∀ t, 1 ≤ x t := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih =>
    rw [dyn t, normal t]
    exact service_step _ _ ih (sum_bounds _ _ _ (eb t).1 (eb t).2.1 (eb t).2.2).2

theorem heat_run (x h e0 e1 e2 : Nat → Int)
    (init : HeatSafe (h 0)) (safe : ∀ t, SpeedSafe (x t))
    (eb : ∀ t, Bit (e0 t) ∧ Bit (e1 t) ∧ Bit (e2 t))
    (dyn : ∀ t, h (t+1) = heat (h t) (e0 t+e1 t+e2 t) (x t)) :
    ∀ t, HeatSafe (h t) := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih =>
    rw [dyn t]
    exact heat_step _ _ _ ih (safe t)
      (sum_bounds _ _ _ (eb t).1 (eb t).2.1 (eb t).2.2)

theorem ablation_trace : speed 4 6 0 = 8 ∧ speed 8 6 0 = 10 ∧
    speed 10 6 0 = 11 ∧ ¬ SpeedSafe 11 := by unfold SpeedSafe; decide

theorem engagement_changes_motion : speed 10 6 0 = 11 ∧ speed 10 6 2 = 9 := by decide

theorem startup_history_matters : ¬ SpeedSafe (speed 10 6 0) := by unfold SpeedSafe; decide

theorem strong_brake_heat_violation : (5*(3:Int) + 3*3*8)/10 = 8 ∧
    ¬ HeatSafe ((5*(3:Int) + 3*3*8)/10) := by unfold HeatSafe; decide

theorem local_effect_pair (sample e0 e1 e2 : Int) (good0 good1 good2 : Prop)
    (budget : (good0 ∧ good1) ∨ (good0 ∧ good2) ∨ (good1 ∧ good2))
    (h0 : good0 → ActsOn sample e0) (h1 : good1 → ActsOn sample e1)
    (h2 : good2 → ActsOn sample e2) : TwoAct sample e0 e1 e2 := by
  rcases budget with h | h | h
  · exact Or.inl ⟨h0 h.1, h1 h.2⟩
  · exact Or.inr (Or.inl ⟨h0 h.1, h2 h.2⟩)
  · exact Or.inr (Or.inr ⟨h1 h.1, h2 h.2⟩)

theorem primitive_transition_total (x h u e : Int) :
    ∃ x' h', x' = speed x u e ∧ h' = heat h e x :=
  ⟨speed x u e, heat h e x, rfl, rfl⟩
theorem shared_heat_composition_failure :
    heat 6 0 4 = 3 ∧ speed 4 6 0 = 8 ∧ speed 4 4 0 = 6 ∧
    (5*(3:Int) + 3*8 + 3*8 + 3*6)/10 = 8 ∧
    ¬ HeatSafe ((5*(3:Int) + 3*8 + 3*8 + 3*6)/10) := by
  unfold HeatSafe
  decide

theorem always_on_can_violate_conduct : ¬ (2 ≤ (1:Int)) := by decide
#print axioms median_sound
#print axioms physical_dichotomy
#print axioms speed_run
#print axioms service_run
#print axioms heat_run
#print axioms issued_on_justified
#print axioms ablation_trace
end ByzantineEnforcement
