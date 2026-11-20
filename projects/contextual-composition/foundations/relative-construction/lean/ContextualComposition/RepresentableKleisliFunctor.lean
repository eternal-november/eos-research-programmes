module
public import ContextualComposition.RepresentableNativeComposition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisli
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
section Horizontal
variable {D : Type*} [Bicategory D] {a b c : D} {f f' f'' : a ⟶ b} {g g' g'' : b ⟶ c}
def horizontal (t : f ⟶ f') (k : g ⟶ g') : (f ≫ g) ⟶ (f' ≫ g') := (t ▷ g) ≫ f' ◁ k
theorem horizontal_id : horizontal (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := by simp [horizontal]
theorem horizontal_comp (t : f ⟶ f') (s : f' ⟶ f'') (k : g ⟶ g') (j : g' ⟶ g'') :
    horizontal (t ≫ s) (k ≫ j) = horizontal t k ≫ horizontal s j := by
  simp only [horizontal,comp_whiskerRight,Bicategory.whiskerLeft_comp,Category.assoc]
  rw [whisker_exchange_assoc]
end Horizontal
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E : B} (T : Data S)
theorem compose_id (f : KH S A D) (g : KH S D E) :
    composeCell T (𝟙 f) (𝟙 g) = 𝟙 (compose T f g) := by
  change horizontal (𝟙 f) ((action S 1).map₂ (𝟙 g)) ▷ M S (yObj E) T.mult = _
  rw [(action S 1).map₂_id,horizontal_id,id_whiskerRight];rfl
theorem compose_comp {f f' f'' : KH S A D} {g g' g'' : KH S D E}
    (t : f ⟶ f') (s : f' ⟶ f'') (k : g ⟶ g') (j : g' ⟶ g'') :
    composeCell T (t ≫ s) (k ≫ j) = composeCell T t k ≫ composeCell T s j := by
  change horizontal (t ≫ s) ((action S 1).map₂ (k ≫ j)) ▷ M S (yObj E) T.mult =
    horizontal t ((action S 1).map₂ k) ▷ M S (yObj E) T.mult ≫
    horizontal s ((action S 1).map₂ j) ▷ M S (yObj E) T.mult
  rw [(action S 1).map₂_comp,horizontal_comp,comp_whiskerRight]
noncomputable def composeFunctor : KH S A D × KH S D E ⥤ KH S A E where
  obj t := compose T t.1 t.2
  map k := composeCell T k.1 k.2
  map_id t := compose_id T t.1 t.2
  map_comp k j := compose_comp T k.1 j.1 k.2 j.2
end ContextualComposition.GrothendieckStep.RepresentableKleisli
