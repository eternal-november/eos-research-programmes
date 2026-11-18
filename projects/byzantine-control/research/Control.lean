import Std

/-! Discrete, integer inventory control. See README.md for the execution contract.
No claim of physical calibration, cryptographic implementation, or asynchronous timing.
All control actions endorsed by a correct actor are computed from its own median. -/
namespace ByzantineControlResearch

def Safe (x : Int) : Prop := 2 ≤ x ∧ x ≤ 8
def Near (x m : Int) : Prop := x - 1 ≤ m ∧ m ≤ x + 1
def Envelope (m z : Int) : Prop := Safe z ∧ m - 1 ≤ z ∧ z ≤ m + 1
def Certified (m u : Int) : Prop :=
  0 ≤ u ∧ u ≤ 2 ∧ ∀ z b : Int, Envelope m z → -1 ≤ b → b ≤ 1 → Safe (z + u - 1 + b)
def common (x : Int) : Int := if x ≤ 4 then 2 else if x = 5 then 1 else 0

def median (a b c : Int) : Int :=
  if a ≤ b then (if b ≤ c then b else if a ≤ c then c else a)
  else (if a ≤ c then a else if b ≤ c then c else b)

theorem median_bound (a b c lo hi : Int)
    (h : ((lo ≤ a ∧ a ≤ hi) ∧ (lo ≤ b ∧ b ≤ hi)) ∨
         ((lo ≤ a ∧ a ≤ hi) ∧ (lo ≤ c ∧ c ≤ hi)) ∨
         ((lo ≤ b ∧ b ≤ hi) ∧ (lo ≤ c ∧ c ≤ hi))) :
    lo ≤ median a b c ∧ median a b c ≤ hi := by
  unfold median
  split <;> split <;> (try split) <;> omega

theorem envelope_covers (x m : Int) (hs : Safe x) (hn : Near x m) : Envelope m x := by
  simp only [Envelope, Safe, Near] at *
  omega

theorem common_certified (x m : Int) (hs : Safe x) (hn : Near x m) :
    Certified m (common x) := by
  unfold Certified common
  split
  · refine ⟨by omega, by omega, ?_⟩
    intro z b hz hb hb'
    simp only [Envelope, Safe, Near] at *
    omega
  · split
    · refine ⟨by omega, by omega, ?_⟩
      intro z b hz hb hb'
      simp only [Envelope, Safe, Near] at *
      omega
    · refine ⟨by omega, by omega, ?_⟩
      intro z b hz hb hb'
      simp only [Envelope, Safe, Near] at *
      omega

theorem certified_step (x m u b : Int) (hs : Safe x) (hn : Near x m)
    (hc : Certified m u) (hb : -1 ≤ b) (hb' : b ≤ 1) :
    Safe (x + u - 1 + b) :=
  hc.2.2 x b (envelope_covers x m hs hn) hb hb'

/- At most one faulty authorizer. A spare identity may be designated bad in a fault-free
run; the theorem then establishes the stronger adversary overapproximation. -/
def Accepted (bad : Fin 3) (med : Fin 3 → Int) (u : Int) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ (i ≠ bad → Certified (med i) u) ∧
    (j ≠ bad → Certified (med j) u)

theorem two_honest (bad : Fin 3) : ∃ i j : Fin 3, i ≠ j ∧ i ≠ bad ∧ j ≠ bad := by
  revert bad
  decide

theorem gate_available (x : Int) (bad : Fin 3) (med : Fin 3 → Int)
    (hs : Safe x) (sound : ∀ i, i ≠ bad → Near x (med i)) :
    Accepted bad med (common x) := by
  obtain ⟨i, j, hij, hi, hj⟩ := two_honest bad
  exact ⟨i, j, hij, fun _ => common_certified x (med i) hs (sound i hi),
    fun _ => common_certified x (med j) hs (sound j hj)⟩

theorem gate_safe (x u b : Int) (bad : Fin 3) (med : Fin 3 → Int)
    (hs : Safe x) (sound : ∀ i, i ≠ bad → Near x (med i))
    (accept : Accepted bad med u) (hb : -1 ≤ b) (hb' : b ≤ 1) :
    Safe (x + u - 1 + b) := by
  obtain ⟨i, j, hij, hi, hj⟩ := accept
  by_cases h : i = bad
  · have hjb : j ≠ bad := by
      intro hj'
      exact hij (h.trans hj'.symm)
    exact certified_step x (med j) u b hs (sound j hjb) (hj hjb) hb hb'
  · exact certified_step x (med i) u b hs (sound i h) (hi h) hb hb'

/- This recurrence is the specified service: exactly one unit is deducted every epoch.
Nonempty accepted actions are supplied by gate_available. Timing/actuator delivery is a
separate operational premise, not inferred from this theorem. -/
theorem loop_invariant (x u b : Nat → Int) (bad : Fin 3) (med : Nat → Fin 3 → Int)
    (init : Safe (x 0))
    (sound : ∀ t i, i ≠ bad → Near (x t) (med t i))
    (accepted : ∀ t, Accepted bad (med t) (u t))
    (bounds : ∀ t, -1 ≤ b t ∧ b t ≤ 1)
    (step : ∀ t, x (t+1) = x t + u t - 1 + b t) :
    ∀ t, Safe (x t) := by
  intro t
  induction t with
  | zero => exact init
  | succ t ih =>
    rw [step t]
    exact gate_safe (x t) (u t) (b t) bad (med t) ih (sound t)
      (accepted t) (bounds t).1 (bounds t).2

/- General adversary families; no counting or independence assumption. -/
def Hits {I : Type} (F : (I → Prop) → Prop) (Q : I → Prop) : Prop :=
  ∀ B, F B → ∃ i, Q i ∧ ¬ B i
def Available {I : Type} (F A : (I → Prop) → Prop) : Prop :=
  ∀ B, F B → ∃ Q, A Q ∧ ∀ i, Q i → ¬ B i
def Q2 {I : Type} (F : (I → Prop) → Prop) : Prop :=
  ∀ B C, F B → F C → ∃ i, ¬ B i ∧ ¬ C i
def Q3 {I : Type} (F : (I → Prop) → Prop) : Prop :=
  ∀ B C D, F B → F C → F D → ∃ i, ¬ B i ∧ ¬ C i ∧ ¬ D i

theorem gate_family_iff_Q2 {I : Type} (F : (I → Prop) → Prop) :
    (∃ A, (∀ Q, A Q → Hits F Q) ∧ Available F A) ↔ Q2 F := by
  constructor
  · rintro ⟨A, hit, avail⟩ B C hB hC
    obtain ⟨Q, hQ, disjoint⟩ := avail B hB
    obtain ⟨i, hi, hCi⟩ := hit Q hQ C hC
    exact ⟨i, disjoint i hi, hCi⟩
  · intro h
    refine ⟨(fun Q => ∃ B, F B ∧ ∀ i, Q i ↔ ¬ B i), ?_, ?_⟩
    · rintro Q ⟨B, hB, eq⟩ C hC
      obtain ⟨i, hi, hj⟩ := h B C hB hC
      exact ⟨i, (eq i).mpr hi, hj⟩
    · intro B hB
      exact ⟨(fun i => ¬ B i), ⟨B, hB, fun _ => Iff.rfl⟩, fun _ hi => hi⟩

theorem conflict_family_iff_Q3 {I : Type} (F : (I → Prop) → Prop) :
    (∃ A, (∀ Q R, A Q → A R → Hits F (fun i => Q i ∧ R i)) ∧ Available F A)
      ↔ Q3 F := by
  constructor
  · rintro ⟨A, hit, avail⟩ B C D hB hC hD
    obtain ⟨Q, hQ, dq⟩ := avail B hB
    obtain ⟨R, hR, dr⟩ := avail C hC
    obtain ⟨i, ⟨hi, hj⟩, hk⟩ := hit Q R hQ hR D hD
    exact ⟨i, dq i hi, dr i hj, hk⟩
  · intro h
    refine ⟨(fun Q => ∃ B, F B ∧ ∀ i, Q i ↔ ¬ B i), ?_, ?_⟩
    · rintro Q R ⟨B, hB, eq⟩ ⟨C, hC, er⟩ D hD
      obtain ⟨i, hi, hj, hk⟩ := h B C D hB hC hD
      exact ⟨i, ⟨(eq i).mpr hi, (er i).mpr hj⟩, hk⟩
    · intro B hB
      exact ⟨(fun i => ¬ B i), ⟨B, hB, fun _ => Iff.rfl⟩, fun _ hi => hi⟩

theorem insufficient_capacity : ∀ u : Int, 0 ≤ u → u ≤ 1 → ¬ Safe (2 + u - 1 + (-1)) := by
  unfold Safe
  omega

theorem excess_removal : ∀ u : Int, 0 ≤ u → u ≤ 2 → ¬ Safe (2 + u - 1 + (-2)) := by
  unfold Safe
  omega

/- A coupled information/noise obstruction: the same median 5 can cover states 2 and 8
when honest error expands to 3; no one command serves both. -/
theorem incompatible_endpoints : ¬ ∃ u : Int, Safe (2 + u - 1 + (-1)) ∧ Safe (8 + u - 1 + 1) := by
  unfold Safe
  omega

/- First-epoch impossibility for two possibly different median-only singleton selectors.
Each pair m,n near the same x is realizable by honest readings x-1,x+1 plus equivocation. -/
theorem no_singleton_median_selectors (f g : Int → Int)
    (valid : ∀ m, 1 ≤ m → m ≤ 9 → Certified m (f m))
    (agree : ∀ x m n, Safe x → Near x m → Near x n → f m = g n) : False := by
  have e1 := agree 2 1 3 (by simp [Safe]) (by simp [Near]) (by simp [Near])
  have e2 := agree 4 5 3 (by simp [Safe]) (by simp [Near]) (by simp [Near])
  have e3 := agree 6 5 7 (by simp [Safe]) (by simp [Near]) (by simp [Near])
  have e4 := agree 8 9 7 (by simp [Safe]) (by simp [Near]) (by simp [Near])
  have lo := (valid 1 (by omega) (by omega)).2.2 2 (-1) (by simp [Envelope, Safe]) (by omega) (by omega)
  have hi := (valid 9 (by omega) (by omega)).2.2 8 1 (by simp [Envelope, Safe]) (by omega) (by omega)
  unfold Safe at lo hi
  omega

#print axioms no_singleton_median_selectors
#print axioms median_bound
#print axioms envelope_covers
#print axioms common_certified
#print axioms certified_step
#print axioms two_honest
#print axioms gate_available
#print axioms gate_safe
#print axioms loop_invariant
#print axioms gate_family_iff_Q2
#print axioms conflict_family_iff_Q3
#print axioms insufficient_capacity
#print axioms excess_removal
#print axioms incompatible_endpoints
end ByzantineControlResearch
