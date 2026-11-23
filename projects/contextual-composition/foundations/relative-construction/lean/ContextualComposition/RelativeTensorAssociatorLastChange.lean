module
public import ContextualComposition.RelativeTensorFourFactors

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable {Y Y' : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY}} (t : Y ⟶ Y')
set_option backward.isDefEq.respectTransparency false

def lastMap : rightInner M Y ⟶ rightInner M Y' :=
  Factorization.Endpoint.Indexed.reindex (Middle.transpose M) (Parametric.vary t)

theorem last_balance {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) (z : Tensor (row M b) Y) :
    (mapSecond (lastMap M t)).map (balancing X (rightInner M Y) u x z).hom =
      (balancing X (rightInner M Y') u x ((mapSecond t).obj z)).hom := by
  rw [Second.on_balance]
  have h : (Second.port (lastMap M t) u z).hom = 𝟙 _ := Parametric.interchange_app (Middle.change M u.op.toLoc) t z
  rw [h]
  change (insertR X M Y' a).map (𝟙 _) ≫ _ = _
  rw [Functor.map_id,Category.id_comp]
  rfl

private theorem pad {D : Type*} [Category* D] {a b : D} {p q : a ⟶ b} (h : p = q) : p ≫ 𝟙 _ = 𝟙 _ ≫ q := by simpa using h

theorem last_inner {c : C} (y : Y.obj ⟨op c⟩) :
    (innerCocone X M Y c y).extend ⋙ mapSecond (lastMap M t) = (innerCocone X M Y' c ((Second.part t c).obj y)).extend := by
  fapply extGenerators
  · intro z; rfl
  · intro b x x' m m' f g
    apply pad
    dsimp only [Functor.comp_map]
    rw [inner_native,Second.on_native,inner_native]
    change (insertR X M Y' b).map (productMap f ((mapSecond t).map ((insertM M Y b c).map (productMap g (𝟙 y))))) = _
    erw [Second.on_native (F := row M b) t g (𝟙 y),Functor.map_id]
  · intro a b u x m
    apply pad
    dsimp only [Functor.comp_map]
    rw [inner_balance,last_balance,inner_balance]
    rfl

theorem last_leaf {c : C} (z : Tensor X (column M c)) {y y' : Y.obj ⟨op c⟩} (f : y ⟶ y') :
    (mapSecond (lastMap M t)).map (leafMap X M Y z f) = leafMap X M Y' z ((Second.part t c).map f) := by
  unfold leafMap
  rw [Second.on_native]
  change (insertR X M Y' z.as.mid).map (productMap _ ((mapSecond t).map ((insertM M Y z.as.mid c).map _))) = _
  erw [Second.on_native (F := row M z.as.mid) t (𝟙 z.as.second) f]

theorem last_native {c : C} {z z' : Tensor X (column M c)} {y y' : Y.obj ⟨op c⟩} (p : z ⟶ z') (q : y ⟶ y') :
    (mapSecond t ⋙ associate X M Y').map ((Reverse.insertL X M Y c).map (productMap p q)) =
      (associate X M Y ⋙ mapSecond (lastMap M t)).map ((Reverse.insertL X M Y c).map (productMap p q)) := by
  dsimp only [Functor.comp_map]
  rw [Second.on_native,associate_native,associate_native,outer_pair,outer_pair,Functor.map_comp,last_leaf]
  congr 1
  have h := Functor.congr_hom (last_inner X M t y') p
  change _ = 𝟙 _ ≫ _ ≫ 𝟙 _ at h
  erw [Category.id_comp,Category.comp_id] at h
  exact h.symm

theorem last_outer_balance {c d : C} (v : c ⟶ d) (z : Tensor X (column M c)) (y : Y.obj ⟨op d⟩) :
    (mapSecond t ⋙ associate X M Y').map (balancing (leftInner X M) Y v z y).hom =
      (associate X M Y ⋙ mapSecond (lastMap M t)).map (balancing (leftInner X M) Y v z y).hom := by
  obtain ⟨⟨b,x,m⟩⟩ := z
  let z := (insertion X (column M c) b).obj (x,m)
  dsimp only [Functor.comp_map]
  change (associate X M Y').map ((mapSecond t).map (balancing (leftInner X M) Y v z y).hom) = _
  rw [Second.on_balance,Functor.map_comp,associate_native,outer_leaf,associate_outer_balance,associate_outer_balance]
  change _ ≫ _ = (mapSecond (lastMap M t)).map ((insertR X M Y b).map (productMap (𝟙 x) (balancing (row M b) Y v m y).hom))
  rw [Second.on_native]
  change (keep X M Y' x).map _ ≫ (keep X M Y' x).map _ = (keep X M Y' x).map ((mapSecond t).map _)
  rw [← Functor.map_comp]
  erw [Second.on_balance (F := row M b) t v m y]
  rfl

/-- Rebracketing commutes with an arbitrary strong comparison on the last factor as a functor on every native arrow and each inverse balance. -/
theorem last_naturality : mapSecond t ⋙ associate X M Y' = associate X M Y ⋙ mapSecond (lastMap M t) := by
  fapply extGenerators
  · intro z; rfl
  · intro c z z' y y' p q; exact pad (last_native X M t p q)
  · intro c d v z y; exact pad (last_outer_balance X M t v z y)

end ContextualComposition.RelativeTensor.Iterated
