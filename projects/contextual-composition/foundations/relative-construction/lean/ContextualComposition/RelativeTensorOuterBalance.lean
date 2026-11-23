module
public import ContextualComposition.RelativeTensorInnerRebracketing

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vX uX vM uM vY uY
variable {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (Y : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vY,uY})
set_option backward.isDefEq.respectTransparency false

abbrev insertR (b : B) := insertion X (rightInner M Y) b
abbrev insertM (b : B) (c : C) := insertion (row M b) Y c

theorem inner_native {b : B} {c : C} (y : Y.obj ⟨op c⟩)
    {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩} (p : x ⟶ x') (q : m ⟶ m') :
    (innerCocone X M Y c y).extend.map ((insertion X (column M c) b).map (productMap p q)) =
      (insertR X M Y b).map (productMap p ((insertM M Y b c).map (productMap q (𝟙 y)))) :=
  (innerCocone X M Y c y).extend_generator (Edge.native (F := X) (G := column M c) p q)

theorem inner_balance {a b : B} {c : C} (u : a ⟶ b) (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩) (y : Y.obj ⟨op c⟩) :
    (innerCocone X M Y c y).extend.map (balancing X (column M c) u x m).hom =
      (balancing X (rightInner M Y) u x ((insertM M Y b c).obj (m,y))).hom :=
  (innerCocone X M Y c y).extend_generator (Edge.balance (F := X) (G := column M c) u x m)

def outerComponent {c d : C} (v : c ⟶ d) (y : Y.obj ⟨op d⟩) (z : Tensor X (column M c)) :
    (innerCocone X M Y c ((backward Y v).obj y)).extend.obj z ≅
      (innerCocone X M Y d y).extend.obj ((forward (leftInner X M) v).obj z) :=
  (insertR X M Y z.as.mid).mapIso ((Iso.refl z.as.first).prod (balancing (row M z.as.mid) Y v z.as.second y))

theorem nativeOuter {c d : C} (v : c ⟶ d) (y : Y.obj ⟨op d⟩) {b : B}
    {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩} (p : x ⟶ x') (q : m ⟶ m') :
    (innerCocone X M Y c ((backward Y v).obj y)).extend.map ((insertion X (column M c) b).map (productMap p q)) ≫
      (outerComponent X M Y v y _).hom =
    (outerComponent X M Y v y _).hom ≫ (innerCocone X M Y d y).extend.map ((forward (leftInner X M) v).map
      ((insertion X (column M c) b).map (productMap p q))) := by
  rw [inner_native,left_native,inner_native]
  change _ ≫ (insertR X M Y b).map _ = (insertR X M Y b).map _ ≫ _
  erw [← (insertR X M Y b).map_comp, ← (insertR X M Y b).map_comp]
  apply congrArg (insertR X M Y b).map
  apply Prod.ext
  · exact (Category.comp_id p).trans (Category.id_comp p).symm
  · have h := (restrict (𝟭 (Tensor (row M b) Y))).natural v q (𝟙 y)
    change (insertM M Y b c).map (productMap q ((backward Y v).map (𝟙 y))) ≫ _ = _ at h
    rw [Functor.map_id] at h
    exact h

private theorem split {b : B} {m n r : (rightInner M Y).obj ⟨op b⟩} (x : X.obj ⟨b⟩) (f : m ⟶ n) (g : n ⟶ r) :
    (insertR X M Y b).map (productMap (𝟙 x) (f ≫ g)) =
      (insertR X M Y b).map (productMap (𝟙 x) f) ≫ (insertR X M Y b).map (productMap (𝟙 x) g) := by
  rw [← Functor.map_comp]
  exact congrArg (insertR X M Y b).map (Prod.ext (Category.id_comp _).symm rfl)

theorem inner_after_C_balance {c d : C} (v : c ⟶ d) (y : Y.obj ⟨op d⟩) {a b : B} (u : a ⟶ b)
    (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩) :
    (innerCocone X M Y d y).extend.map ((forward (leftInner X M) v).map (balancing X (column M c) u x m).hom) =
      (insertR X M Y a).map (productMap (𝟙 x) ((insertM M Y a d).map (productMap (Second.port (M.map v.toLoc) u m).hom (𝟙 y)))) ≫
      (balancing X (rightInner M Y) u x ((insertM M Y b d).obj (((M.map v.toLoc).app ⟨op b⟩).toFunctor.obj m,y))).hom := by
  change (innerCocone X M Y d y).extend.map ((mapSecond (M.map v.toLoc)).map _) = _
  erw [Second.on_balance,Functor.map_comp,inner_native,inner_balance]

/-- The two middle balances pass one another using the actual mixed square of M. -/
theorem mixedSquare {c d : C} (v : c ⟶ d) (y : Y.obj ⟨op d⟩) {a b : B} (u : a ⟶ b)
    (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩) :
    (innerCocone X M Y c ((backward Y v).obj y)).extend.map (balancing X (column M c) u x m).hom ≫
      (outerComponent X M Y v y _).hom =
    (outerComponent X M Y v y _).hom ≫ (innerCocone X M Y d y).extend.map
      ((forward (leftInner X M) v).map (balancing X (column M c) u x m).hom) := by
  let zm := (balancing (row M b) Y v m y).hom
  let S := restrict (𝟭 (Right X M Y))
  have h := S.natural u (𝟙 x) zm
  change (insertR X M Y a).map (productMap (𝟙 x) ((mapFirst (Middle.change M u.op.toLoc)).map zm)) ≫ _ =
    _ ≫ (insertR X M Y b).map (productMap ((forward X u).map (𝟙 x)) zm) at h
  dsimp only [zm] at h
  erw [First.on_balance, split X M Y, Category.assoc, Functor.map_id] at h
  rw [inner_after_C_balance,inner_balance]
  exact h.symm

def outerSquare {c d : C} (v : c ⟶ d) (y : Y.obj ⟨op d⟩) :
    (innerCocone X M Y c ((backward Y v).obj y)).extend ≅
      (forward (leftInner X M) v) ⋙ (innerCocone X M Y d y).extend :=
  isoOfGenerators (outerComponent X M Y v y) (fun p q => nativeOuter X M Y v y p q)
    (fun u x m => mixedSquare X M Y v y u x m)

end ContextualComposition.RelativeTensor.Iterated
