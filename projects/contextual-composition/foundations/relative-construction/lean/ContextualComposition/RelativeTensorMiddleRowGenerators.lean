module
public import ContextualComposition.RelativeTensorMiddleRowChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem identify_insertion {F G : LocallyDiscrete D ⥤ᵖ Cat.{vN,uN}} (h : F = G) (d : D) (p : F.obj ⟨d⟩ = G.obj ⟨d⟩) :
    insertion F Y d ⋙ (identifyFirst h Y).functor = ((eqToHom p).toFunctor.prod (𝟭 _)) ⋙ insertion G Y d := by
  subst G; rfl

private theorem identify_balance {F G : LocallyDiscrete D ⥤ᵖ Cat.{vN,uN}} (h : F = G) {d e : D} (v : d ⟶ e)
    (x : F.obj ⟨d⟩) (x' : G.obj ⟨d⟩) (hx : HEq x x') (y : Y.obj ⟨op e⟩) :
    HEq ((identifyFirst h Y).functor.mapIso (balancing F Y v x y)) (balancing G Y v x' y) := by
  subst G; cases eq_of_heq hx; rfl

/-- The complete product insertion commutes with the row identification, including every arrow of the inner tensor. -/
theorem middleRow_insertion (b : B) (d : D) :
    insertion (row (middleComposite M N) b) Y d ⋙ (identifyFirst (middleRow M N b) Y).functor =
      insertion (leftInner (row M b) N) Y d :=
  identify_insertion Y (middleRow M N b) d (congrArg (fun F => F.obj ⟨d⟩) (middleRow_pre M N b))

/-- Transport of the inserted object keeps its entire inner tensor representative and terminal payload. -/
theorem middleRow_object (b : B) (d : D) (x : Tensor (row M b) (column N d)) (y : Y.obj ⟨op d⟩) :
    (identifyFirst (middleRow M N b) Y).functor.obj ((insertion (row (middleComposite M N) b) Y d).obj (x,y)) =
      (insertion (leftInner (row M b) N) Y d).obj (x,y) :=
  Functor.congr_obj (middleRow_insertion M N Y b d) (x,y)

/-- Comparison of native arrows with both object transports, allowing arbitrary morphisms of the inner localized tensor. -/
theorem middleRow_native (b : B) (d : D) {x x' : Tensor (row M b) (column N d)} {y y' : Y.obj ⟨op d⟩}
    (f : x ⟶ x') (g : y ⟶ y') :
    (identifyFirst (middleRow M N b) Y).functor.map ((insertion (row (middleComposite M N) b) Y d).map (productMap f g)) =
      eqToHom (middleRow_object M N Y b d x y) ≫ (insertion (leftInner (row M b) N) Y d).map (productMap f g) ≫
        eqToHom (middleRow_object M N Y b d x' y').symm :=
  Functor.congr_hom (middleRow_insertion M N Y b d) (productMap f g)

/-- On primitive coordinates this identifies the two whole product functors at fixed middle objects. -/
theorem middleRow_primitive (b : B) (c : C) (d : D) :
    ((insertion (row M b) (column N d) c).prod (𝟭 (Y.obj ⟨op d⟩))) ⋙
      insertion (row (middleComposite M N) b) Y d ⋙ (identifyFirst (middleRow M N b) Y).functor =
    ((insertion (row M b) (column N d) c).prod (𝟭 (Y.obj ⟨op d⟩))) ⋙ insertion (leftInner (row M b) N) Y d :=
  congrArg (((insertion (row M b) (column N d) c).prod (𝟭 (Y.obj ⟨op d⟩))) ⋙ ·) (middleRow_insertion M N Y b d)

private theorem frame_iso {T : Type*} [Category* T] {a b a' b' : T} (i : a ≅ b) (j : a' ≅ b')
    (p : a = a') (q : b = b') (h : HEq i j) : i = eqToIso p ≪≫ j ≪≫ (eqToIso q).symm := by
  subst a'; subst b'; cases eq_of_heq h; simp

/-- The full D-balance isomorphism, in either direction, is preserved with the displayed endpoint transports. -/
theorem middleRow_balance (b : B) {d e : D} (v : d ⟶ e) (x : Tensor (row M b) (column N d)) (y : Y.obj ⟨op e⟩) :
    (identifyFirst (middleRow M N b) Y).functor.mapIso (balancing (row (middleComposite M N) b) Y v x y) =
      eqToIso (middleRow_object M N Y b d x ((backward Y v).obj y)) ≪≫ balancing (leftInner (row M b) N) Y v x y ≪≫
        (eqToIso (middleRow_object M N Y b e ((forward (leftInner (row M b) N) v).obj x) y)).symm := by
  apply frame_iso
  exact identify_balance Y (middleRow M N b) v x x HEq.rfl y

end ContextualComposition.RelativeTensor.Iterated
