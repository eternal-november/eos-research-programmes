import QuotientArrowCertificates
import WitnessedDecompositions.RefinementExamples

/-! Instantiation of the new tuple/derivability bridge on the ACTUAL B2 mixed
interface quotient, not an assumed category or a shadow Arrow definition. -/
namespace WitnessedDecompositions.Integration
open RefinementExamples

theorem actual_mixed_entries_not_all_derivable :
    ¬ (∀ i, Presentation.Derives S equations
      (rawRepresentative equations (mixedLeftArrow.val i))
      (rawRepresentative equations (mixedRightArrow.val i))) := by
  intro h
  exact mixed_unequal_parallel_arrows
    ((arrow_eq_iff_entry_derives equations mixedLeftArrow mixedRightArrow).mpr h)

/-- The composite endpoint alone agrees on both histories; it does not justify
replacing the entrywise criterion by equality of evaluated totals. -/
theorem actual_mixed_equal_endpoints :
    M.subst (projection.map mixedSource) mixedLeftArrow.val =
      M.subst (projection.map mixedSource) mixedRightArrow.val :=
  mixedLeftArrow.property.trans mixedRightArrow.property.symm

end WitnessedDecompositions.Integration
