module
public import ContextualComposition.AmbientHorizontalFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientHorizontalDiagrams
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
variable {X Y : Obj.{u,v} B}
noncomputable abbrev K (f : X ⟶ Y) := AmbientBicategory.map S 1 f
theorem twice (f : X ⟶ Y) : K S (K S f) = AmbientBicategory.map S 2 f :=
  InducedBicategory.hom_ext (AmbientBlockIteration.blockSucc S f.hom 1)
noncomputable def squareM (f : X ⟶ Y) : K S (K S f) ≫ M S Y m ≅ M S X m ≫ K S f :=
  eqToIso (congrArg (· ≫ M S Y m) (twice S f)) ≪≫ comparison S (tensor m) m.cart f
noncomputable def squareE (f : X ⟶ Y) : f ≫ E S Y d ≅ E S X d ≫ K S f :=
  eqToIso (congrArg (· ≫ E S Y d) (InducedBicategory.hom_ext (AmbientBlockIteration.blockZero S f.hom)).symm) ≪≫ comparison S (insert S d) (unitCart d) f
section General
variable {C : Type*} [Bicategory C] [Bicategory.Strict C]
variable {x y z : C} {a b : x ⟶ y} {f g g' : y ⟶ z}
def reAssoc {w : C} (p : w ⟶ x) {t u : x ⟶ y} (q : y ⟶ z) {a : w ⟶ y} (e : a ≅ p ≫ t) (h : t ≅ u) :
    a ≫ q ≅ p ≫ u ≫ q := whiskerRightIso e q ≪≫ (α_ p t q) ≪≫ whiskerLeftIso p (whiskerRightIso h q)
def middle {w : C} (p : w ⟶ x) (t : x ⟶ y) (q : y ⟶ z) {t' : x ⟶ y} {q' : y ⟶ z} (h : t ≫ q ≅ t' ≫ q') :
    (p ≫ t) ≫ q ≅ (p ≫ t') ≫ q' := (α_ p t q) ≪≫ whiskerLeftIso p h ≪≫ (α_ p t' q').symm
def foldMap (F : StrictPseudofunctor C C) {z' : C} {p : x ⟶ y} {q : y ⟶ z} {t : x ⟶ z'} {u : z' ⟶ z} (s : p ≫ q ≅ t ≫ u) :
    F.map p ≫ F.map q ≅ F.map t ≫ F.map u := (F.mapComp p q).symm ≪≫ F.map₂Iso s ≪≫ F.mapComp t u
def foldUnit (F : StrictPseudofunctor C C) {p : x ⟶ y} {q : y ⟶ x} (s : p ≫ q ≅ 𝟙 x) :
    F.map p ≫ F.map q ≅ 𝟙 (F.obj x) := (F.mapComp p q).symm ≪≫ F.map₂Iso s ≪≫ F.mapId x
end General
variable (X)
noncomputable def triLong :=
  middle (K S (E S (obj S 1 X) d)) _ _ (assoc S X d m c) ≪≫
  whiskerRightIso (foldUnit (action S 1) (left S X d m c)) (M S X m) ≪≫ (λ_ _)
noncomputable def triShort := whiskerRightIso (right S (obj S 1 X) d m c) (M S X m) ≪≫ (λ_ _)
noncomputable def pentLong :=
  whiskerRightIso (assoc S (obj S 1 X) d m c) (M S X m) ≪≫
  middle (K S (M S (obj S 1 X) m)) _ _ (assoc S X d m c) ≪≫
  whiskerRightIso (foldMap (action S 1) (assoc S X d m c)) (M S X m)
noncomputable def pentShort :=
  middle (M S (obj S 2 X) m) _ _ (assoc S X d m c) ≪≫
  whiskerRightIso (squareM S m (M S X m)).symm (M S X m) ≪≫
  middle (K S (K S (M S X m))) _ _ (assoc S X d m c)
abbrev Triangle : Prop := (triLong S d m c X).hom = (triShort S d m c X).hom
abbrev Pentagon : Prop := (pentLong S d m c X).hom = (pentShort S d m c X).hom
end ContextualComposition.GrothendieckStep.AmbientHorizontalDiagrams
