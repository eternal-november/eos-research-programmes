import Std

/-! Fault-indexed handover, fallible authorization, and a make-before-break
peer-brake substitution. The executable-to-stream adapter is stated in ENACTMENT.md.
No cryptographic implementation, hardware repair, or mobile-fault theorem is assumed. -/
namespace ByzantineEnactment

def Bit (x : Int) : Prop := 0 ≤ x ∧ x ≤ 1

def speed (x u e : Int) : Int := max 0 ((5*x + 10*u - 10*e) / 10)
def heat (h e x : Int) : Int := (5*h + e*x) / 10
def command (x : Int) : Int := if 2 ≤ x then 1 else 0
def Safe (x : Int) : Prop := 0 ≤ x ∧ x ≤ 10
def HeatSafe (h : Int) : Prop := 0 ≤ h ∧ h ≤ 8

/- A single program is fixed before the fault argument. Step is its actual
closed-loop relation, including every admitted supplier effect, not a permission
filter. Modes label contracts; the theorem does not select or reveal them. -/
theorem fault_indexed_handover
    {Fault Program State Mode Event : Type}
    (program : Program)
    (Step : Fault → Program → State → Event → State → Prop)
    (Entry : Fault → Mode → State → Prop)
    (Mission : Fault → State → Event → State → Prop)
    (edge : ∀ f m s e s', Entry f m s → Step f program s e s' →
      ∃ m', Entry f m' s' ∧ Mission f s e s')
    (f : Fault) (states : Nat → State) (events : Nat → Event)
    (start : ∃ m, Entry f m (states 0))
    (run : ∀ t, Step f program (states t) (events t) (states (t+1))) :
    (∀ t, ∃ m, Entry f m (states t)) ∧
    (∀ t, Mission f (states t) (events t) (states (t+1))) := by
  have entries : ∀ t, ∃ m, Entry f m (states t) := by
    intro t
    induction t with
    | zero => exact start
    | succ t ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨m', hm', _⟩ := edge f m _ _ _ hm (run t)
      exact ⟨m', hm'⟩
  exact ⟨entries, fun t => by
    obtain ⟨m, hm⟩ := entries t
    obtain ⟨_, _, hmission⟩ := edge f m _ _ _ hm (run t)
    exact hmission⟩

/- Nonblocking remains separate: an entry has an actual move and an admitted
successor. In particular a declined installation cannot become an empty relation. -/
theorem entry_nonblocking
    {Fault Program State Mode Event : Type}
    (program : Program) (Step : Fault → Program → State → Event → State → Prop)
    (Entry : Fault → Mode → State → Prop)
    (available : ∀ f m s, Entry f m s → ∃ e s', Step f program s e s')
    (f : Fault) (m : Mode) (s : State) (h : Entry f m s) :
    ∃ e s', Step f program s e s' := available f m s h

/- Two distinct signatures include a path outside the executor/key-fault union.
The premise connects uncompromised paths to operational guarded issuance. -/
theorem threshold_ready (a0 a1 a2 v0 v1 v2 ready : Int)
    (ha0 : Bit a0) (ha1 : Bit a1) (ha2 : Bit a2)
    (hv0 : Bit v0) (hv1 : Bit v1) (hv2 : Bit v2) (hr : Bit ready)
    (budget : a0+a1+a2 ≤ 1) (quorum : 2 ≤ v0+v1+v2)
    (sound0 : a0=0 → v0=1 → ready=1)
    (sound1 : a1=0 → v1=1 → ready=1)
    (sound2 : a2=0 → v2=1 → ready=1) : ready=1 := by
  unfold Bit at *
  omega

/- Accepted artifacts and actual executor-issued signatures are separate.
Compromising a key does not remove its executor from the compliant set. -/
theorem threshold_intact_vote (a0 a1 a2 v0 v1 v2 : Int)
    (ha0 : Bit a0) (ha1 : Bit a1) (ha2 : Bit a2)
    (hv0 : Bit v0) (hv1 : Bit v1) (hv2 : Bit v2)
    (budget : a0+a1+a2 ≤ 1) (quorum : 2 ≤ v0+v1+v2) :
    (a0=0 ∧ v0=1) ∨ (a1=0 ∧ v1=1) ∨ (a2=0 ∧ v2=1) := by
  unfold Bit at *
  omega

theorem threshold_guarded_issue
    (exec0 exec1 exec2 key0 key1 key2 v0 v1 v2 issued0 issued1 issued2 ready : Int)
    (he0 : Bit exec0) (he1 : Bit exec1) (he2 : Bit exec2)
    (hk0 : Bit key0) (hk1 : Bit key1) (hk2 : Bit key2)
    (hv0 : Bit v0) (hv1 : Bit v1) (hv2 : Bit v2)
    (budget : max exec0 key0 + max exec1 key1 + max exec2 key2 ≤ 1)
    (quorum : 2 ≤ v0+v1+v2)
    (path0 : exec0=0 → key0=0 → v0=1 → issued0=1)
    (path1 : exec1=0 → key1=0 → v1=1 → issued1=1)
    (path2 : exec2=0 → key2=0 → v2=1 → issued2=1)
    (guard0 : exec0=0 → issued0=1 → ready=1)
    (guard1 : exec1=0 → issued1=1 → ready=1)
    (guard2 : exec2=0 → issued2=1 → ready=1) :
    (exec0=0 ∧ key0=0 ∧ issued0=1 ∧ ready=1) ∨
    (exec1=0 ∧ key1=0 ∧ issued1=1 ∧ ready=1) ∨
    (exec2=0 ∧ key2=0 ∧ issued2=1 ∧ ready=1) := by
  have maxBit : ∀ e k : Int, Bit e → Bit k → Bit (max e k) := by
    intro e k he hk
    unfold Bit at *
    omega
  have zeros : ∀ e k : Int, Bit e → Bit k → max e k=0 → e=0 ∧ k=0 := by
    intro e k he hk hz
    unfold Bit at *
    omega
  have hit := threshold_intact_vote (max exec0 key0) (max exec1 key1) (max exec2 key2)
    v0 v1 v2 (maxBit _ _ he0 hk0) (maxBit _ _ he1 hk1) (maxBit _ _ he2 hk2)
    hv0 hv1 hv2 budget quorum
  rcases hit with h0 | h1 | h2
  · have z := zeros _ _ he0 hk0 h0.1
    have actual := path0 z.1 z.2 h0.2
    exact Or.inl ⟨z.1, z.2, actual, guard0 z.1 actual⟩
  · have z := zeros _ _ he1 hk1 h1.1
    have actual := path1 z.1 z.2 h1.2
    exact Or.inr (Or.inl ⟨z.1, z.2, actual, guard1 z.1 actual⟩)
  · have z := zeros _ _ he2 hk2 h2.1
    have actual := path2 z.1 z.2 h2.2
    exact Or.inr (Or.inr ⟨z.1, z.2, actual, guard2 z.1 actual⟩)

/- READY need not prove that the spare is healthy. Its fault-indexed disjunction
is enough: a false READY spends the very chain-fault allowance that would otherwise
endanger a surviving old chain. Old channel 2 may retire without a certificate only
when that chain is faulty. Every engagement remains independently adversarial. -/
theorem surviving_pair
    (b0 b1 b2 b3 retired ready warm e0 e1 e2 e3 old : Int)
    (hb0 : Bit b0) (hb1 : Bit b1) (hb2 : Bit b2) (hb3 : Bit b3)
    (he0 : Bit e0) (he1 : Bit e1) (he2 : Bit e2) (he3 : Bit e3)
    (hret : Bit retired) (hr : Bit ready) (hw : Bit warm)
    (budget : b0+b1+b2+b3 ≤ 1)
    (retireWarrant : retired=1 → b2=1 ∨ ready=1)
    (readyWarrant : ready=1 → b3=1 ∨ warm=1)
    (track0 : b0=0 → 2 ≤ old → e0=1)
    (track1 : b1=0 → 2 ≤ old → e1=1)
    (track2 : b2=0 → retired=0 → 2 ≤ old → e2=1)
    (track3 : b3=0 → warm=1 → 2 ≤ old → e3=1) :
    2 ≤ e0+e1+e2+e3 ∨ old ≤ 1 := by
  unfold Bit at *
  omega

/- A general disjoint replacement slot may use its retained old channel or its
acknowledged spare. A faulty member can invalidate one slot, never a free reset. -/
theorem replacement_slot
    (badOld badNew retired ready warm oldEffect newEffect : Int)
    (bo : Bit badOld) (bn : Bit badNew) (r : Bit retired) (rd : Bit ready)
    (w : Bit warm) (eo : Bit oldEffect) (en : Bit newEffect)
    (retireWarrant : retired=1 → badOld=1 ∨ ready=1)
    (readyWarrant : ready=1 → badNew=1 ∨ warm=1)
    (oldTracks : badOld=0 → retired=0 → oldEffect=1)
    (newTracks : badNew=0 → warm=1 → newEffect=1) :
    1 ≤ oldEffect+newEffect+badOld+badNew := by
  unfold Bit at *
  omega

theorem sum_slot_coverage {A : Type} (slots : List A) (live bad : A → Nat)
    (coverage : ∀ i, i ∈ slots → 1 ≤ live i + bad i) :
    slots.length ≤ (slots.map live).sum + (slots.map bad).sum := by
  induction slots with
  | nil => simp
  | cons head tail ih =>
    have hh := coverage head (by simp)
    have ht := ih (fun i hi => coverage i (by simp [hi]))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem replacement_family_bound {A : Type} (slots : List A)
    (live bad : A → Nat) (f totalEffect : Nat)
    (coverage : ∀ i, i ∈ slots → 1 ≤ live i + bad i)
    (jointBudget : (slots.map bad).sum ≤ f)
    (actualEffects : (slots.map live).sum ≤ totalEffect) :
    slots.length - f ≤ totalEffect := by
  have h := sum_slot_coverage slots live bad coverage
  omega

theorem engaged_parameter_step (x u e V T survivors : Int)
    (hx : 0 ≤ x ∧ x ≤ V) (hu : u ≤ T) (he : survivors ≤ e)
    (margin : 2*T-2*survivors ≤ V) :
    0 ≤ speed x u e ∧ speed x u e ≤ V := by
  unfold speed
  omega

theorem service_parameter_step (x u e maximum : Int)
    (hx : 1 ≤ x) (he : e ≤ maximum) (supply : maximum+1 ≤ u) :
    1 ≤ speed x u e := by
  unfold speed
  omega

theorem command_bounds (x : Int) : Bit (command x) := by
  unfold command Bit
  split <;> omega

theorem issued_on_justified (x : Int) (h : command x = 1) : 2 ≤ x := by
  unfold command at h
  split at h <;> omega

theorem majority_threshold (truth a b c : Int)
    (ht : Bit truth) (ha : Bit a) (hb : Bit b) (hc : Bit c)
    (sound : (a=truth ∧ b=truth) ∨ (a=truth ∧ c=truth) ∨ (b=truth ∧ c=truth)) :
    (if 2 ≤ a+b+c then (1 : Int) else 0) = truth := by
  unfold Bit at *
  split <;> omega

theorem startup_safe (x u e : Int) (hx : 0 ≤ x ∧ x ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 7) (he : 0 ≤ e) : Safe (speed x u e) := by
  unfold Safe speed
  omega

theorem low_successor (x u e : Int) (hx : x ≤ 1) (hu : u ≤ 7)
    (he : 0 ≤ e) : speed x u e ≤ 7 := by
  unfold speed
  omega

theorem engaged_step (x u e : Int) (hx : Safe x) (hu : u ≤ 7)
    (he : 2 ≤ e) : Safe (speed x u e) := by
  unfold Safe speed at *
  omega

theorem recent_step (x u e : Int) (hx : x ≤ 7) (hu : u ≤ 7)
    (he : 0 ≤ e) : Safe (speed x u e) := by
  unfold Safe speed
  omega

theorem delayed_step (old current oldU oldE u e : Int)
    (hcur : Safe current) (hprev : current = speed old oldU oldE)
    (holdU : oldU ≤ 7) (holdE : 0 ≤ oldE) (hu : u ≤ 7) (he : 0 ≤ e)
    (pair : 2 ≤ e ∨ old ≤ 1) : Safe (speed current u e) := by
  rcases pair with high | low
  · exact engaged_step current u e hcur hu high
  · have hc : current ≤ 7 := by
      rw [hprev]
      exact low_successor old oldU oldE low holdU holdE
    exact recent_step current u e hc hu he

theorem service_step (x e : Int) (hx : 1 ≤ x) (he : e ≤ 4) :
    1 ≤ speed x 5 e := by
  unfold speed
  omega

theorem heat_load_step (h load capacity : Int)
    (hh : 0 ≤ h ∧ h ≤ capacity) (hl : 0 ≤ load ∧ load ≤ 5*capacity) :
    0 ≤ (5*h+load)/10 ∧ (5*h+load)/10 ≤ capacity := by
  omega

theorem heat_step (h e x : Int) (hh : HeatSafe h) (hx : Safe x)
    (he : 0 ≤ e ∧ e ≤ 4) : HeatSafe (heat h e x) := by
  have cases : e=0 ∨ e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;>
    unfold heat HeatSafe Safe at * <;> omega

theorem speed_run (x u e : Nat → Int)
    (init : 0 ≤ x 0 ∧ x 0 ≤ 1)
    (ub : ∀ t, 0 ≤ u t ∧ u t ≤ 7)
    (eb : ∀ t, 0 ≤ e t ∧ e t ≤ 4)
    (effect : ∀ t, x (t+1) = speed (x t) (u t) (e t))
    (coverage : ∀ t, 2 ≤ e (t+1) ∨ x t ≤ 1) : ∀ t, Safe (x t) := by
  intro t
  induction t with
  | zero => unfold Safe; omega
  | succ t ih =>
    cases t with
    | zero => rw [effect]; exact startup_safe _ _ _ init (ub 0) (eb 0).1
    | succ k =>
      rw [effect (k+1)]
      exact delayed_step (x k) (x (k+1)) (u k) (e k) (u (k+1)) (e (k+1))
        ih (effect k) (ub k).2 (eb k).1 (ub (k+1)).2 (eb (k+1)).1 (coverage k)

theorem service_run (x e : Nat → Int) (init : 1 ≤ x 0)
    (eb : ∀ t, e t ≤ 4) (effect : ∀ t, x (t+1) = speed (x t) 5 (e t)) :
    ∀ t, 1 ≤ x t := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih => rw [effect]; exact service_step _ _ ih (eb t)

theorem heat_run (x h e : Nat → Int) (init : HeatSafe (h 0))
    (xs : ∀ t, Safe (x t)) (eb : ∀ t, 0 ≤ e t ∧ e t ≤ 4)
    (effect : ∀ t, h (t+1) = heat (h t) (e t) (x t)) :
    ∀ t, HeatSafe (h t) := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih => rw [effect]; exact heat_step _ _ _ ih (xs t) (eb t)

/- One remaining old channel, an absent replacement and legal hostile drive.
These are the actual physical transitions, not a verifier-filtered relation. -/
theorem wrong_order_trace :
    speed 1 7 0 = 7 ∧ speed 7 7 0 = 10 ∧ speed 10 7 1 = 11 := by decide

theorem all_four_preserve_normal_service : speed 1 5 4 = 1 := by decide

theorem shared_heat_boundary : heat 8 4 10 = 8 := by decide

#print axioms fault_indexed_handover
#print axioms entry_nonblocking
#print axioms threshold_ready
#print axioms threshold_intact_vote
#print axioms threshold_guarded_issue
#print axioms surviving_pair
#print axioms replacement_slot
#print axioms sum_slot_coverage
#print axioms replacement_family_bound
#print axioms engaged_parameter_step
#print axioms service_parameter_step
#print axioms command_bounds
#print axioms issued_on_justified
#print axioms majority_threshold
#print axioms startup_safe
#print axioms low_successor
#print axioms engaged_step
#print axioms recent_step
#print axioms delayed_step
#print axioms service_step
#print axioms heat_load_step
#print axioms heat_step
#print axioms speed_run
#print axioms service_run
#print axioms heat_run
#print axioms wrong_order_trace
#print axioms all_four_preserve_normal_service
#print axioms shared_heat_boundary
end ByzantineEnactment
