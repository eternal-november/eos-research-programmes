module
public import ContextualComposition.RelativeTensorFactorCells

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
variable {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G G' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable (s : Pseudofunctor.StrongTrans F F') (t : Pseudofunctor.StrongTrans G G')
set_option backward.isDefEq.respectTransparency false

def mapBoth : Tensor F G ⥤ Tensor F' G' := mapFirst s ⋙ mapSecond t

theorem mapBoth_native {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (p : x ⟶ x') (q : y ⟶ y') :
    (mapBoth s t).map ((insertion F G i).map (productMap p q)) =
      (insertion F' G' i).map (productMap ((First.part s i).map p) ((Second.part t i).map q)) := by
  dsimp only [mapBoth,Functor.comp_map]
  rw [First.on_native, Second.on_native]

/-- The two comparison ports sit on opposite sides of the same target balance. -/
theorem mapBoth_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (mapBoth s t).map (balancing F G u x y).hom =
      (insertion F' G' i).map (productMap (𝟙 ((First.part s i).obj x)) (Second.port t u y).hom) ≫
      (balancing F' G' u ((First.part s i).obj x) ((Second.part t j).obj y)).hom ≫
      (insertion F' G' j).map (productMap (First.port s u x).hom (𝟙 ((Second.part t j).obj y))) := by
  dsimp only [mapBoth,Functor.comp_map]
  rw [First.on_balance, Functor.map_comp, Second.on_balance, Second.on_native, Functor.map_id, Category.assoc]

theorem factor_order_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (mapBoth s t).map (balancing F G u x y).hom = (mapFirst s).map ((mapSecond t).map (balancing F G u x y).hom) := by
  rw [mapBoth_balance, Second.on_balance, Functor.map_comp, First.on_native, First.on_balance, Functor.map_id]

/-- The two orders agree on the entire quotient functor, including inverse balances and composite paths. -/
theorem factor_order : mapBoth s t = mapSecond t ⋙ mapFirst s := by
  apply CategoryTheory.Quotient.lift_unique'
  fapply Paths.ext_functor
  · rfl
  intro x y g
  cases g with
  | native f g =>
    change (mapBoth s t).map ((insertion F G _).map (productMap f g)) =
      𝟙 _ ≫ (mapFirst s).map ((mapSecond t).map ((insertion F G _).map (productMap f g))) ≫ 𝟙 _
    erw [Category.id_comp,Category.comp_id,mapBoth_native]
  | balance u x y =>
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]
    exact factor_order_balance s t u x y
  | unbalance u x y =>
    change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]
    have h : (mapBoth s t).mapIso (balancing F G u x y) = (mapSecond t ⋙ mapFirst s).mapIso (balancing F G u x y) :=
      Iso.ext (factor_order_balance s t u x y)
    exact congrArg Iso.inv h

end ContextualComposition.RelativeTensor
