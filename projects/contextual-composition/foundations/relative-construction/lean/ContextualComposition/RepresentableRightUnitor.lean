module
public import ContextualComposition.RepresentableKleisliConstraints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableRightUnitor
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad AmbientHorizontalDiagrams
open RepresentableKleisli RepresentableKleisliConstraints
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
section Generic
variable {C : Type*} [Bicategory C] {a b c : C} {f g : a ⟶ b} {p : b ⟶ c} {q : c ⟶ b}
theorem natural (t : f ⟶ g) (r : p ≫ q ≅ 𝟙 b) :
    ((t ▷ p) ▷ q) ≫ ((α_ g p q) ≪≫ whiskerLeftIso g r ≪≫ (ρ_ g)).hom =
    ((α_ f p q) ≪≫ whiskerLeftIso f r ≪≫ (ρ_ f)).hom ≫ t := by
  have assoc : ((t ▷ p) ▷ q) ≫ (α_ g p q).hom = (α_ f p q).hom ≫ t ▷ (p ≫ q) := by
    rw [Bicategory.whiskerRight_comp]; simp
  have exchange : t ▷ (p ≫ q) ≫ g ◁ r.hom = f ◁ r.hom ≫ t ▷ 𝟙 b :=
    (whisker_exchange t r.hom).symm
  simp only [Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  rw [← Category.assoc ((t ▷ p) ▷ q),assoc,Category.assoc,← Category.assoc (t ▷ (p ≫ q)),exchange]
  simp
end Generic
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable (T : Data S) {A D : B} {f g : KH S A D} (k : f ⟶ g)
theorem original :
    composeCell T k (𝟙 (unit T D)) ≫ (rightUnit T g).hom = (rightUnit T f).hom ≫ k := by
  have one : composeCell T k (𝟙 (unit T D)) = (k ▷ K S (unit T D)) ▷ M S (yObj D) T.mult := by
    change ((k ▷ K S (unit T D)) ≫ g ◁ (action S 1).map₂ (𝟙 (unit T D))) ▷ M S (yObj D) T.mult = _
    rw [(action S 1).map₂_id]
    change ((k ▷ K S (unit T D)) ≫ g ◁ (𝟙 (K S (unit T D)))) ▷ M S (yObj D) T.mult = _
    rw [Bicategory.whiskerLeft_id,Category.comp_id]
  rw [one]
  exact natural k (rightIso T (yObj D))
end ContextualComposition.GrothendieckStep.RepresentableRightUnitor
