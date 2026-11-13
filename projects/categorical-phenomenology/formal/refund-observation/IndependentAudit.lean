import OrderedGroupRefunds
import BoundedRefunds
import ClassicalGroupCorollary
import PreorderControl
set_option autoImplicit false
namespace IndependentAudit
open ResourceObservation
universe u

-- A literal classification for arbitrary predicates yields excluded middle.
-- Thus the classical qualification cannot simply be removed from the report.
theorem literal_classification_implies_em {G : Type u}
    (g : OrderedAbelianGroupData G)
    (classify : ∀ B : Profile G, UniversalProductAgreement g.add g.le B →
      (∀ b, ¬ B b) ∨ (∀ b, B b)) (P : Prop) : P ∨ ¬ P := by
  have agreement : UniversalProductAgreement g.add g.le (fun _ => P) :=
    (g.universal_agreement_iff_nonempty_forces_all _).mpr (fun _ h _ => h)
  rcases classify (fun _ => P) agreement with empty | all
  · exact Or.inr (empty g.zero)
  · exact Or.inl (all g.zero)

-- Vacuous windows are correct even with completely empty input observations.
theorem below_lower_sum (l r C : Int) (h : C < l+r) :
    BoundedUniversalAgreement l r C (fun _ => False) (fun _ => False) := by
  apply (bounded_universal_agreement_iff_coverage l r C _ _).mpr
  constructor
  · intro a ha; obtain ⟨h1,h2⟩ := ha; omega
  · intro b hb; obtain ⟨h1,h2⟩ := hb; omega

-- No information is lost by observing [l+r,C] instead of all budgets ≤ C:
-- below l+r both products are impossible, independently of upward closure.
theorem output_agreement_extends_below (l r C : Int)
    (U U' V V' : Profile Int)
    (lowU : LowerBounded l U) (lowU' : LowerBounded l U')
    (lowV : LowerBounded r V) (lowV' : LowerBounded r V')
    (same : AgreeOn (IntWindow (l+r) C)
      (Product Int.add (· ≤ ·) U V) (Product Int.add (· ≤ ·) U' V')) :
    AgreeOn (fun z => z ≤ C)
      (Product Int.add (· ≤ ·) U V) (Product Int.add (· ≤ ·) U' V') := by
  intro z hz
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    have hl := lowU x hx
    have hr := lowV y hy
    have sum : x+y ≤ z := hxy
    have lower : l+r ≤ z := by omega
    exact (same z ⟨lower,hz⟩).mp ⟨x,y,hx,hy,hxy⟩
  · rintro ⟨x,y,hx,hy,hxy⟩
    have hl := lowU' x hx
    have hr := lowV' y hy
    have sum : x+y ≤ z := hxy
    have lower : l+r ≤ z := by omega
    exact (same z ⟨lower,hz⟩).mpr ⟨x,y,hx,hy,hxy⟩

-- Omitting just one endpoint invalidates universal reconstruction even when
-- every other integer is observed. This checks the inclusive threshold.
theorem missing_left_endpoint (l r C : Int) (h : l+r ≤ C) :
    ¬ BoundedUniversalAgreement l r C (fun a => a ≠ C-r) (fun _ => True) := by
  intro agreement
  have required := bounded_agreement_forces_left_coverage l r C _ _ agreement
    (C-r) ⟨by omega, Int.le_refl _⟩
  exact required rfl

theorem missing_right_endpoint (l r C : Int) (h : l+r ≤ C) :
    ¬ BoundedUniversalAgreement l r C (fun _ => True) (fun b => b ≠ C-l) := by
  intro agreement
  have required := bounded_agreement_forces_right_coverage l r C _ _ agreement
    (C-l) ⟨by omega, Int.le_refl _⟩
  exact required rfl

#print axioms literal_classification_implies_em
#print axioms below_lower_sum
#print axioms output_agreement_extends_below
#print axioms missing_left_endpoint
#print axioms missing_right_endpoint
end IndependentAudit
