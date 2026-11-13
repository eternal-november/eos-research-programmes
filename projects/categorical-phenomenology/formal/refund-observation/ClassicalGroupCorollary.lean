/- Literal empty/full classification under Lean's standard classical logic.
This is separate from the axiom-free constructive main theorem. -/
import OrderedGroupRefunds
set_option autoImplicit false
universe u
namespace ResourceObservation.OrderedAbelianGroupData
variable {G : Type u}

theorem universal_agreement_iff_empty_or_all
    (g : OrderedAbelianGroupData G) (B : Profile G) :
    UniversalProductAgreement g.add g.le B ↔
      (∀ b, ¬ B b) ∨ (∀ b, B b) := by
  classical
  exact g.universal_agreement_iff_empty_or_all_decidable B

#print axioms universal_agreement_iff_empty_or_all
end ResourceObservation.OrderedAbelianGroupData
