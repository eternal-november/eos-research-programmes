import Std

/-! Selected integer/discrete kernels. Physical source and interpreter refinements
remain the explicit obligations in INFORMATION.md. Timestamps are proof ghosts. -/
namespace LocalInformation

theorem count_all {α : Type} (p : α → Bool) (xs : List α)
    (all : ∀ x ∈ xs, p x = true) : xs.countP p = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := all a (by simp)
    have ht : ∀ x ∈ xs, p x = true := fun x hx => all x (by simp [hx])
    simp [ha, ih ht]

theorem quorum_has_good_witness {α : Type} (votes : List α) (bad : α → Bool)
    (b : Nat) (enough : b < votes.length) (budget : votes.countP bad ≤ b) :
    ∃ x ∈ votes, bad x = false := by
  classical
  by_cases h : ∃ x ∈ votes, bad x = false
  · exact h
  · have hall : ∀ x ∈ votes, bad x = true := by
      intro x hx
      cases hb : bad x with
      | false => exact False.elim (h ⟨x, hx, hb⟩)
      | true => rfl
    have hc := count_all bad votes hall
    omega

theorem uncontaminated_path_margin (n b contaminated : Nat)
    (size : n = 2*b+1) (bound : contaminated ≤ b) :
    b+1 ≤ n-contaminated := by omega

theorem union_footprint_budget (sizes : List Nat) (reach : Nat)
    (each : ∀ n ∈ sizes, n ≤ reach) : sizes.sum ≤ reach*sizes.length := by
  induction sizes with
  | nil => simp
  | cons a tail ih =>
    have ha := each a (by simp)
    have ht : ∀ n ∈ tail, n ≤ reach := fun n hn => each n (by simp [hn])
    have hb := ih ht
    simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

structure Cache where
  sampled : Nat
  expires : Nat

def CacheBound (state : Option Cache) (age : Nat) : Prop :=
  ∀ c, state = some c → c.expires ≤ c.sampled+age

inductive CacheStep (conversion lifetime : Nat) : Option Cache → Option Cache → Prop
  | wait (state) : CacheStep conversion lifetime state state
  | query (state) : CacheStep conversion lifetime state state
  | clear (state) : CacheStep conversion lifetime state none
  | completed (state) (sampled completed : Nat)
      (delay : completed ≤ sampled+conversion) :
      CacheStep conversion lifetime state (some ⟨sampled, completed+lifetime⟩)

theorem cache_bound_preserved (conversion lifetime : Nat) (before after : Option Cache)
    (bound : CacheBound before (conversion+lifetime))
    (step : CacheStep conversion lifetime before after) :
    CacheBound after (conversion+lifetime) := by
  cases step with
  | wait => exact bound
  | query => exact bound
  | clear => simp [CacheBound]
  | completed sampled completed delay =>
    intro c hc
    cases hc
    simp only
    omega

theorem live_cache_age (c : Cache) (now age : Nat)
    (bound : c.expires ≤ c.sampled+age) (live : now < c.expires) :
    now-c.sampled ≤ age := by omega

theorem bounded_actual_age (sample emitted received decoded used S C D E U : Nat)
    (source : emitted ≤ sample+S+C)
    (path : received ≤ emitted+D)
    (vote : decoded ≤ received+E)
    (use : used ≤ decoded+U) :
    used-sample ≤ S+C+D+E+U := by omega

theorem permission_guard (load gap medianLoad medianGap betaLoad betaGap limit minGap : Int)
    (loadCover : load ≤ medianLoad+betaLoad)
    (gapCover : medianGap-betaGap ≤ gap)
    (loadGuard : medianLoad+betaLoad ≤ limit)
    (gapGuard : minGap ≤ medianGap-betaGap) :
    load ≤ limit ∧ minGap ≤ gap := by omega

theorem permission_margin_composition (load sample median error drift jump limit : Int)
    (measurement : sample ≤ median+error)
    (variation : load ≤ sample+drift+jump)
    (guard : median+error+drift+jump ≤ limit) : load ≤ limit := by omega

theorem common_action_sound {State Action : Type} (alternatives : State → Prop)
    (permitted : State → Action → Prop) (actual : State) (action : Action)
    (contains : alternatives actual)
    (common : ∀ x, alternatives x → permitted x action) : permitted actual action :=
  common actual contains

theorem primary_changes_permission : (97 : Int)+3 ≤ 100 ∧ ¬ ((99 : Int)+3 ≤ 100) := by decide

theorem low_load_and_isolation_permitted : (60 : Int)+3 ≤ 100 ∧ 80 ≤ (90 : Int)-2 := by decide

theorem high_load_refused : ¬ ((120 : Int)+3 ≤ 100) := by decide

end LocalInformation
