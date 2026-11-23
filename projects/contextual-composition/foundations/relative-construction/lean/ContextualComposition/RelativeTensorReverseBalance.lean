module
public import ContextualComposition.RelativeTensorReverseInner

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.Reverse
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

def outerComponent {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) (z : Tensor (row M b) Y) :
    (innerCocone X M Y x).extend.obj ((backward (rightInner M Y) u).obj z) ≅
      (innerCocone X M Y ((forward X u).obj x)).extend.obj z :=
  (insertL X M Y z.as.mid).mapIso ((balancing X (column M z.as.mid) u x z.as.first).prod (Iso.refl z.as.second))

theorem nativeOuter {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) {c : C}
    {m m' : (column M c).obj ⟨op b⟩} {y y' : Y.obj ⟨op c⟩} (p : m ⟶ m') (q : y ⟶ y') :
    (innerCocone X M Y x).extend.map ((backward (rightInner M Y) u).map
      ((insertion (row M b) Y c).map (productMap p q))) ≫ (outerComponent X M Y u x _).hom =
    (outerComponent X M Y u x _).hom ≫ (innerCocone X M Y ((forward X u).obj x)).extend.map
      ((insertion (row M b) Y c).map (productMap p q)) := by
  rw [right_native,inner_native,inner_native]
  change (insertL X M Y c).map _ ≫ (insertL X M Y c).map _ = (insertL X M Y c).map _ ≫ (insertL X M Y c).map _
  erw [← (insertL X M Y c).map_comp,← (insertL X M Y c).map_comp]
  apply congrArg (insertL X M Y c).map
  apply Prod.ext
  · have h := (restrict (𝟭 (Tensor X (column M c)))).natural u (𝟙 x) p
    change _ = _ ≫ (insertM X M b c).map (productMap ((forward X u).map (𝟙 x)) p) at h
    rw [Functor.map_id] at h
    exact h
  · exact (Category.comp_id q).trans (Category.id_comp q).symm

private theorem split {c : C} {m n r : (leftInner X M).obj ⟨c⟩} (y : Y.obj ⟨op c⟩) (f : m ⟶ n) (g : n ⟶ r) :
    (insertL X M Y c).map (productMap (f ≫ g) (𝟙 y)) =
      (insertL X M Y c).map (productMap f (𝟙 y)) ≫ (insertL X M Y c).map (productMap g (𝟙 y)) := by
  rw [← Functor.map_comp]
  exact congrArg (insertL X M Y c).map (Prod.ext rfl (Category.id_comp _).symm)

theorem inner_after_B_balance {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) {c d : C} (v : c ⟶ d)
    (m : (column M c).obj ⟨op b⟩) (y : Y.obj ⟨op d⟩) :
    (innerCocone X M Y x).extend.map ((backward (rightInner M Y) u).map (balancing (row M b) Y v m y).hom) =
      (balancing (leftInner X M) Y v ((insertM X M a c).obj (x,(backward (column M c) u).obj m)) y).hom ≫
      (insertL X M Y d).map (productMap ((insertM X M a d).map (productMap (𝟙 x) (Second.port (M.map v.toLoc) u m).hom)) (𝟙 y)) := by
  change (innerCocone X M Y x).extend.map ((mapFirst (Middle.change M u.op.toLoc)).map _) = _
  erw [First.on_balance, Functor.map_comp, inner_native, inner_balance]
  rfl

theorem mixedSquare {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) {c d : C} (v : c ⟶ d)
    (m : (column M c).obj ⟨op b⟩) (y : Y.obj ⟨op d⟩) :
    (innerCocone X M Y x).extend.map ((backward (rightInner M Y) u).map (balancing (row M b) Y v m y).hom) ≫
      (outerComponent X M Y u x _).hom =
    (outerComponent X M Y u x _).hom ≫ (innerCocone X M Y ((forward X u).obj x)).extend.map (balancing (row M b) Y v m y).hom := by
  let zm := (balancing X (column M c) u x m).hom
  have h := (restrict (𝟭 (Left X M Y))).natural v zm (𝟙 y)
  change (insertL X M Y c).map (productMap zm ((backward Y v).map (𝟙 y))) ≫ _ =
    _ ≫ (insertL X M Y d).map (productMap ((mapSecond (M.map v.toLoc)).map zm) (𝟙 y)) at h
  dsimp only [zm] at h
  erw [Second.on_balance,split X M Y, Functor.map_id] at h
  rw [inner_after_B_balance,inner_balance,Category.assoc]
  exact h.symm

def outerSquare {a b : B} (u : a ⟶ b) (x : X.obj ⟨a⟩) :
    (backward (rightInner M Y) u) ⋙ (innerCocone X M Y x).extend ≅ (innerCocone X M Y ((forward X u).obj x)).extend :=
  isoOfGenerators (outerComponent X M Y u x) (fun p q => nativeOuter X M Y u x p q) (fun v m y => mixedSquare X M Y u x v m y)

end ContextualComposition.RelativeTensor.Iterated.Reverse
