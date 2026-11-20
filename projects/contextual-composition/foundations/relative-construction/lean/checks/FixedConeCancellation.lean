import ContextualComposition.AmbientChartRows
open CategoryTheory ContextualComposition.GrothendieckStep
open TelescopeSquares FibreValue NativeCleavage
namespace FixedConeCancellation
inductive O | point
instance : Category O where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev p := O.point
def swap : p ⟶ p := not
def stop : p ⟶ p := fun _ => false
def π := (Functor.const O).obj (Discrete.mk PUnit.unit)
theorem parallelBase : π.map swap = π.map (𝟙 p) := rfl
theorem absorbed : swap ≫ stop = 𝟙 p ≫ stop := rfl
theorem swapIso : IsIso swap := ⟨swap, by funext x; cases x <;> rfl, by funext x; cases x <;> rfl⟩
theorem swapNe : swap ≠ 𝟙 p := fun e => Bool.noConfusion (congrFun e false)
theorem originalNotCartesian : ¬ Cartesian π stop :=
  fun h => swapNe (ContextadOuterCharts.cancel π stop h _ _ parallelBase absorbed)
end FixedConeCancellation
#print axioms FixedConeCancellation.originalNotCartesian
namespace FixedConeCancellation
theorem identityCart {a b : O} (f : a ⟶ b) : Cartesian (𝟭 O) f := by
  intro z g v h
  exact ⟨v,⟨rfl,h.symm⟩,fun t u => u.1⟩
theorem sameNonMonicLeg : Cartesian (𝟭 O) stop ∧ swap ≫ stop = (𝟙 p) ≫ stop ∧ swap ≠ 𝟙 p :=
  ⟨identityCart stop,absorbed,swapNe⟩
theorem identificationFails : ¬ Aligned ((𝟭 O).map swap) ((𝟭 O).map (𝟙 p)) := fun h => swapNe h.eq
end FixedConeCancellation
#print axioms FixedConeCancellation.sameNonMonicLeg
#print axioms FixedConeCancellation.identificationFails
