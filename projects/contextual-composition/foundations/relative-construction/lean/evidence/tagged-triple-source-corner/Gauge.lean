import ContextualComposition.TaggedTripleCover
open CategoryTheory
namespace TargetGaugeProbe
inductive D where | point
instance : Category D where
  Hom _ _ := Bool
  id _ := false
  comp f g := Bool.xor f g
  id_comp := by intros x y f; cases f <;> rfl
  comp_id := by intros x y f; cases f <;> rfl
  assoc := by intros a b c d f g h; cases f <;> cases g <;> cases h <;> rfl
def twist : 𝟭 D ⟶ 𝟭 D where
  app _ := true
  naturality := by intros x y f; change Bool.xor f true = Bool.xor true f; cases f <;> rfl
def targetAlternative : 𝟭 D ≅ 𝟭 D where
  hom := twist
  inv := twist
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl
example : (𝟙 (𝟭 D)) ≫ targetAlternative.hom ≠ (𝟙 (𝟭 D)) ≫ (𝟙 (𝟭 D)) := by
  intro h
  have b : true = false := NatTrans.congr_app h D.point
  cases b
-- All four corner isomorphisms may be identities, and all first three edge
-- tests pass; the independently chosen fourth edge need not commute.
example : (𝟙 (𝟭 D)) ≫ targetAlternative.hom ≠ (𝟙 (𝟭 D)) ≫ (𝟙 (𝟭 D)) := by
  intro h; exact Bool.noConfusion (NatTrans.congr_app h D.point)
-- Conversely a pair of 'independent' bad boundary edges can be hidden if
-- frames are chosen retrospectively: use twist at B only.
example : targetAlternative.hom ≫ targetAlternative.hom = 𝟙 _ ∧
    targetAlternative.hom ≫ (𝟙 (𝟭 D)) = targetAlternative.hom ≫ (𝟙 (𝟭 D)) :=
  ⟨targetAlternative.hom_inv_id,rfl⟩
end TargetGaugeProbe
