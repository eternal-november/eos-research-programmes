module
public import ContextualComposition.CanonicalSetStrength
public import ContextualComposition.EmptyFrameNecessity
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! The empty-frame necessity argument on actual Set interfaces. Both uses of invertibility are derived from pure maps between empty carriers and the chosen comparison of the pure and framed object actions. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.EmptyFramePureMaps
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
universe u w v z
variable {B : Type z} [Bicategory.{w,v} B]

def cancelPairs {a b c : B} {i : a ⟶ b} {j : b ⟶ c} {i' : b ⟶ a} {j' : c ⟶ b}
    (hi : i' ≫ i ≅ 𝟙 b) (hj : j' ≫ j ≅ 𝟙 c) : (j' ≫ i') ≫ (i ≫ j) ≅ 𝟙 c :=
  (α_ _ _ _) ≪≫ whiskerLeftIso j' ((α_ i' i j).symm ≪≫ whiskerRightIso hi j ≪≫ λ_ j) ≪≫ hj

variable (J : LocallyDiscrete (Type u) ⥤ᵖ B)
abbrev O (X : Type u) := J.obj ⟨X⟩
abbrev pure {X Y : Type u} (f : X ⟶ Y) := J.map f.toLoc
abbrev Zero := PEmpty.{u+1}
def initial (Y : Type u) : Zero.{u} ⟶ Y := TypeCat.ofHom PEmpty.elim

def cancelPure {X Y : Type u} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) :
    pure J f ≫ pure J g ≅ 𝟙 (O J X) :=
  (J.mapComp f.toLoc g.toLoc).symm ≪≫ eqToIso (congrArg (pure J) h) ≪≫ J.mapId _

def emptyProjection : Zero.{u} × Zero.{u} ≅ Zero.{u} where
  hom := TypeCat.ofHom Prod.snd
  inv := TypeCat.ofHom PEmpty.elim
  hom_inv_id := by apply ConcreteCategory.hom_ext; intro x; exact x.1.elim
  inv_hom_id := by apply ConcreteCategory.hom_ext; intro x; exact x.elim

def framedInitial (Y : Type u) : Zero.{u} × Zero.{u} ≅ Zero.{u} × Y where
  hom := (CanonicalSetStrength.frame Zero).map (initial Y)
  inv := TypeCat.ofHom fun x => x.1.elim
  hom_inv_id := by apply ConcreteCategory.hom_ext; intro x; exact x.1.elim
  inv_hom_id := by apply ConcreteCategory.hom_ext; intro x; exact x.1.elim

variable (S : B ⥤ᵖ B) (θ : Pseudofunctor.StrongTrans S (Pseudofunctor.id B)) (Y : Type u)
variable (atZero : Bicategory.Equivalence (S.obj (O J Zero.{u})) (O J (Zero.{u} × Zero.{u})))
variable (atY : Bicategory.Equivalence (S.obj (O J Y)) (O J (Zero.{u} × Y)))
variable (parameter : θ.app (O J Zero) ≅ atZero.hom ≫ pure J emptyProjection.hom)
variable (preservesPure : S.map (pure J (initial Y)) ≫ atY.hom ≅ atZero.hom ≫ pure J (framedInitial Y).hom)

include parameter preservesPure in
/-- These are the empty-to-unit parameter and empty-frame pure comparisons of the action. Neither assumes that transport on a content fibre is an equivalence. -/
def intrinsic : (O J Zero ⟶ O J Zero) ≌ (O J Zero ⟶ O J Y) := by
  let X := O J Zero
  let y := O J Y
  let e := pure J (initial Y)
  let k := pure J emptyProjection.inv ≫ atZero.inv
  have kθ : k ≫ θ.app X ≅ 𝟙 X :=
    whiskerLeftIso k parameter ≪≫ cancelPairs atZero.counit
      (cancelPure J emptyProjection.inv emptyProjection.hom emptyProjection.inv_hom_id)
  let source := S.obj X
  let p := framedInitial Y
  let P := EmptyFrameNecessity.postEquivalence source (pure J p.hom) (pure J p.inv)
    (cancelPure J _ _ p.hom_inv_id) (cancelPure J _ _ p.inv_hom_id)
  let A := EmptyFrameNecessity.postEquivalence source atZero.hom atZero.inv atZero.unit.symm atZero.counit
  let D := EmptyFrameNecessity.postEquivalence source atY.hom atY.inv atY.unit.symm atY.counit
  let R := postcomp source (S.map e)
  have square : R ⋙ D.functor ≅ A.functor ⋙ P.functor :=
    associatorNatIsoLeft source (S.map e) atY.hom ≪≫ (postcomposing source _ _).mapIso preservesPure ≪≫
      (associatorNatIsoLeft source atZero.hom (pure J p.hom)).symm
  letI : (R ⋙ D.functor).IsEquivalence := Functor.isEquivalence_of_iso square.symm
  letI : R.IsEquivalence := Functor.isEquivalence_of_comp_right R D.functor
  exact EmptyFrameNecessity.retractEquivalence (postcomp X e) R.asEquivalence
    (S.mapFunctor X X) (S.mapFunctor X y) (EmptyFrameNecessity.returnHom S θ k X)
    (EmptyFrameNecessity.returnHom S θ k y) (EmptyFrameNecessity.mapPost S e)
    (EmptyFrameNecessity.returnPost S θ k e) (EmptyFrameNecessity.returnIso S θ k kθ X)
    (EmptyFrameNecessity.returnIso S θ k kθ y)

end ContextualComposition.EmptyFramePureMaps
