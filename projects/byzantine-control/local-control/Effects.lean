import Std

/-! Selected source-refinement obligations for EFFECTS.md. -/
namespace ByzantineEffects

theorem guarded_realization {Issue Contact : Type}
    (actual : Issue → Contact → Prop)
    (possible justified : Issue → Contact → Prop)
    (good : Contact → Prop)
    (effectSound : ∀ a p, actual a p → possible a p)
    (guardCoverage : ∀ a p, possible a p → justified a p)
    (guardSound : ∀ a p, justified a p → good p) :
    ∀ a p, actual a p → good p := by
  intro a p h
  exact guardSound a p (guardCoverage a p (effectSound a p h))

theorem recent_issue_supplies_conduct {Issue Contact : Type}
    (field : Contact → Prop) (witness : Issue → Contact → Prop)
    (good : Contact → Prop)
    (recent : ∀ p, field p → ∃ a, witness a p)
    (guarded : ∀ a p, witness a p → good p) :
    ∀ p, field p → good p := by
  intro p h
  obtain ⟨a, ha⟩ := recent p h
  exact guarded a p ha

theorem heterogeneous_fold {Contact : Type}
    (actual report error : Contact → Int) (fold margin limit : Int)
    (envelope : ∀ p, actual p ≤ report p + error p)
    (foldUpper : ∀ p, report p ≤ fold)
    (marginUpper : ∀ p, error p ≤ margin)
    (guard : fold + margin ≤ limit) : ∀ p, actual p ≤ limit := by
  intro p
  have he := envelope p
  have hf := foldUpper p
  have hm := marginUpper p
  omega

theorem peak_member_bound (actual report peak margin : Int)
    (peakBound : actual ≤ peak) (nonnegativeReport : 0 ≤ report)
    (marginCoversPeak : peak ≤ margin) : actual ≤ report + margin := by omega

theorem sample_to_effect_horizon (sample issue effect age life : Int)
    (sampleAge : issue-age ≤ sample) (effectLife : effect ≤ issue+life) :
    effect-sample ≤ age+life := by omega

inductive Path {V : Type} (edge : V → V → Prop) : V → V → Prop where
  | refl (v) : Path edge v v
  | step {a b c} : edge a b → Path edge b c → Path edge a c

theorem path_monotone {V : Type} (actual upper : V → V → Prop)
    (contained : ∀ a b, actual a b → upper a b) :
    ∀ a b, Path actual a b → Path upper a b := by
  intro a b h
  induction h with
  | refl v => exact Path.refl v
  | step he _ ih => exact Path.step (contained _ _ he) ih

theorem reach_certificate {V : Type} (actual upper : V → V → Prop)
    (allowed : V → V → Prop)
    (contained : ∀ a b, actual a b → upper a b)
    (certificate : ∀ a b, Path upper a b → allowed a b) :
    ∀ a b, Path actual a b → allowed a b := by
  intro a b h
  exact certificate a b (path_monotone actual upper contained a b h)

/- Scaled rational flow bounds; actual-output intervals and source support
   are supplied by the separate component/plant refinement. -/
theorem weighted_upper_boundary (m b p : Int)
    (population : 72 ≤ m) (bad : b ≤ 6) (physical : p ≤ 1) :
    199*100*m ≤ 300*(86*(m-b)-100*(b+3*p)) := by omega

theorem weighted_lower_boundary (m b p : Int)
    (population : 72 ≤ m) (bad : b ≤ 6) (physical : p ≤ 1) :
    300*(34*(m-b)+100*(b+3*p)) ≤ 131*100*m := by omega

theorem weighted_service (m b p : Int)
    (population : 72 ≤ m) (bad : b ≤ 6) (physical : p ≤ 1) :
    3*100*m ≤ 20*(30*(m-b)-100*(b+3*p)) := by omega

theorem weighted_upper_collar (m b p : Int)
    (population : 72 ≤ m) (bad : b ≤ 6) (physical : p ≤ 1) :
    11*10000*m ≤ 2500*(100*(84*(m-b)-100*(b+3*p))-6406*m) := by omega

theorem weighted_lower_collar (m b p : Int)
    (population : 72 ≤ m) (bad : b ≤ 6) (physical : p ≤ 1) :
    261*10000*m ≤ 2500*(5594*m-100*(36*(m-b)+100*(b+3*p))) := by omega

#print axioms guarded_realization
#print axioms recent_issue_supplies_conduct
#print axioms heterogeneous_fold
#print axioms peak_member_bound
#print axioms sample_to_effect_horizon
#print axioms path_monotone
#print axioms reach_certificate
#print axioms weighted_upper_boundary
#print axioms weighted_lower_boundary
#print axioms weighted_service
#print axioms weighted_upper_collar
#print axioms weighted_lower_collar
end ByzantineEffects
