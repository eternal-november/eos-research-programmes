module
public import ContextualComposition.PrimitiveBalance
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Products.Basic
@[expose] public section
namespace ContextualComposition.Factorization.Source
open CategoryTheory CategoryTheory.Functor
universe vK vL vC vD uK uL uC uD
variable {K : Type uK} {L : Type uL} {C : Type uC} {D : Type uD}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C] [Category.{vD} D]
variable (e : K ⥤ C) (d : L ⥤ C)

/-- A native product arrow at a literally fixed middle object. -/
@[ext] structure ProductHom (s t : Object e d) where
  left : s.left ⟶ t.left
  right : s.right ⟶ t.right
  middle_eq : s.middle = t.middle
  first_square : e.map left ≫ t.first = s.first ≫ eqToHom middle_eq
  second_square : eqToHom middle_eq ≫ t.second = s.second ≫ d.map right

/-- Equality transport is retained explicitly; no arbitrary middle map occurs. -/
def productArrow {s t : Object e d} (f : ProductHom e d s t) : s ⟶ t :=
  ⟨f.left, eqToHom f.middle_eq, f.right, f.first_square, f.second_square⟩

def productId (s : Object e d) : ProductHom e d s s :=
  ⟨𝟙 _, 𝟙 _, rfl, by simp, by simp⟩

def productComp {s t r : Object e d} (f : ProductHom e d s t)
    (g : ProductHom e d t r) : ProductHom e d s r where
  left := f.left ≫ g.left
  right := f.right ≫ g.right
  middle_eq := f.middle_eq.trans g.middle_eq
  first_square := by
    rw [Functor.map_comp, Category.assoc, g.first_square, ← Category.assoc,
      f.first_square, Category.assoc, eqToHom_trans]
  second_square := by
    rw [← eqToHom_trans f.middle_eq g.middle_eq, Category.assoc, g.second_square, ← Category.assoc,
      f.second_square, Functor.map_comp, Category.assoc]

@[simp] theorem productArrow_id (s : Object e d) :
    productArrow e d (productId e d s) = 𝟙 s := by apply Factorization.Hom.ext <;> rfl
@[simp] theorem productArrow_comp {s t r : Object e d}
    (f : ProductHom e d s t) (g : ProductHom e d t r) :
    productArrow e d (productComp e d f g) = productArrow e d f ≫ productArrow e d g := by
  apply Factorization.Hom.ext
  · rfl
  · exact (eqToHom_trans f.middle_eq g.middle_eq).symm
  · rfl


/-- Native product corrections for equality of representatives. -/
def productEq {s t : Object e d} (h : s = t) : ProductHom e d s t := by
  subst t
  exact productId e d s
@[simp] theorem productArrow_eq {s t : Object e d} (h : s = t) :
    productArrow e d (productEq e d h) = eqToHom h := by subst t; simp [productEq]


/-- Literal product-category arrow, with independent input/output native maps. -/
def native {Z : C} {P P' : K} {Q Q' : L}
    (x : e.obj P ⟶ Z) (x' : e.obj P' ⟶ Z)
    (y : Z ⟶ d.obj Q) (y' : Z ⟶ d.obj Q')
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hx : e.map α ≫ x' = x) (hy : y ≫ d.map β = y') :
    ProductHom e d ⟨Z,P,Q,x,y⟩ ⟨Z,P',Q',x',y'⟩ :=
  ⟨α, β, rfl, by simpa using hx, by simpa using hy.symm⟩

def balanceUnit {Z : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (y : Z ⟶ d.obj Q) :=
  native e d x (x ≫ 𝟙 Z) (𝟙 Z ≫ y) y (𝟙 P) (𝟙 Q) (by simp) (by simp)

def balanceAssocLeft {Z Z' Z'' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (v : Z' ⟶ Z'') (y : Z'' ⟶ d.obj Q) :=
  native e d x x ((u ≫ v) ≫ y) (u ≫ (v ≫ y)) (𝟙 P) (𝟙 Q)
    (by simp) (by simp [Category.assoc])
def balanceAssocRight {Z Z' Z'' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (v : Z' ⟶ Z'') (y : Z'' ⟶ d.obj Q) :=
  native e d ((x ≫ u) ≫ v) (x ≫ (u ≫ v)) y y (𝟙 P) (𝟙 Q)
    (by simp [Category.assoc]) (by simp)

def balanceNativeLeft {Z Z' : C} {P P' : K} {Q Q' : L}
    (x : e.obj P ⟶ Z) (x' : e.obj P' ⟶ Z) (u : Z ⟶ Z')
    (y : Z' ⟶ d.obj Q) (y' : Z' ⟶ d.obj Q')
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hx : e.map α ≫ x' = x) (hy : y ≫ d.map β = y') :=
  native e d x x' (u ≫ y) (u ≫ y') α β hx (by rw [Category.assoc, hy])
def balanceNativeRight {Z Z' : C} {P P' : K} {Q Q' : L}
    (x : e.obj P ⟶ Z) (x' : e.obj P' ⟶ Z) (u : Z ⟶ Z')
    (y : Z' ⟶ d.obj Q) (y' : Z' ⟶ d.obj Q')
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hx : e.map α ≫ x' = x) (hy : y ≫ d.map β = y') :=
  native e d (x ≫ u) (x' ≫ u) y y' α β (by rw [← Category.assoc, hx]) hy

/-- Independently specified source cocone: product functoriality, invertible
balances, and exactly balance unit/composition/naturality relations.
No action on a general three-map factorization arrow is an input. -/
structure Cocone where
  obj : Object e d → D
  map : ∀ {s t}, ProductHom e d s t → (obj s ⟶ obj t)
  map_id : ∀ s, map (productId e d s) = 𝟙 (obj s)
  map_comp : ∀ {s t r} (f : ProductHom e d s t) (g : ProductHom e d t r),
    map (productComp e d f g) = map f ≫ map g
  bal : ∀ {Z Z' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (y : Z' ⟶ d.obj Q),
    obj ⟨Z,P,Q,x,u ≫ y⟩ ≅ obj ⟨Z',P,Q,x ≫ u,y⟩
  bal_id : ∀ {Z : C} {P : K} {Q : L} (x : e.obj P ⟶ Z) (y : Z ⟶ d.obj Q),
    (bal x (𝟙 Z) y).hom = map (balanceUnit e d x y)
  bal_comp : ∀ {Z Z' Z'' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (v : Z' ⟶ Z'') (y : Z'' ⟶ d.obj Q),
    (bal x (u ≫ v) y).hom =
      map (balanceAssocLeft e d x u v y) ≫
      (bal x u (v ≫ y)).hom ≫ (bal (x ≫ u) v y).hom ≫
      map (balanceAssocRight e d x u v y)
  bal_natural : ∀ {Z Z' : C} {P P' : K} {Q Q' : L}
    (x : e.obj P ⟶ Z) (x' : e.obj P' ⟶ Z) (u : Z ⟶ Z')
    (y : Z' ⟶ d.obj Q) (y' : Z' ⟶ d.obj Q')
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hx : e.map α ≫ x' = x) (hy : y ≫ d.map β = y'),
    map (balanceNativeLeft e d x x' u y y' α β hx hy) ≫ (bal x' u y').hom =
      (bal x u y).hom ≫ map (balanceNativeRight e d x x' u y y' α β hx hy)


variable {e d}
/-- A cocone transformation is compatible with product maps and balance maps. -/
@[ext] structure Transformation (S T : Cocone e d (D := D)) where
  app : ∀ s, S.obj s ⟶ T.obj s
  native_naturality : ∀ {s t} (f : ProductHom e d s t),
    S.map f ≫ app t = app s ≫ T.map f
  balance_naturality : ∀ {Z Z' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (y : Z' ⟶ d.obj Q),
    (S.bal x u y).hom ≫ app _ = app _ ≫ (T.bal x u y).hom

instance coconeCategory : Category (Cocone e d (D := D)) where
  Hom := Transformation
  id S := ⟨fun _ => 𝟙 _, by intros; simp, by intros; simp⟩
  comp f g :=
    { app := fun s => f.app s ≫ g.app s
      native_naturality := by
        intro s t h
        rw [← Category.assoc, f.native_naturality, Category.assoc,
          g.native_naturality, Category.assoc]
      balance_naturality := by
        intros
        rw [← Category.assoc, f.balance_naturality, Category.assoc,
          g.balance_naturality, Category.assoc] }
  id_comp f := by apply Transformation.ext; funext s; exact Category.id_comp _
  comp_id f := by apply Transformation.ext; funext s; exact Category.comp_id _
  assoc f g h := by apply Transformation.ext; funext s; exact Category.assoc _ _ _

variable (e d)
/-- The source balance relations hold among the actual factorization arrows. -/
theorem balance_unit_arrow {Z : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (y : Z ⟶ d.obj Q) :
    balance e d P Q x (𝟙 Z) y = productArrow e d (balanceUnit e d x y) := by
  apply Factorization.Hom.ext <;> rfl

theorem balance_comp_arrow {Z Z' Z'' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (v : Z' ⟶ Z'') (y : Z'' ⟶ d.obj Q) :
    balance e d P Q x (u ≫ v) y =
      productArrow e d (balanceAssocLeft e d x u v y) ≫
      balance e d P Q x u (v ≫ y) ≫ balance e d P Q (x ≫ u) v y ≫
      productArrow e d (balanceAssocRight e d x u v y) := by
  apply Factorization.Hom.ext
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _; simp
  · change u ≫ v = 𝟙 _ ≫ u ≫ v ≫ 𝟙 _; simp
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _; simp

theorem balance_natural_arrow {Z Z' : C} {P P' : K} {Q Q' : L}
    (x : e.obj P ⟶ Z) (x' : e.obj P' ⟶ Z) (u : Z ⟶ Z')
    (y : Z' ⟶ d.obj Q) (y' : Z' ⟶ d.obj Q')
    (α : P ⟶ P') (β : Q ⟶ Q')
    (hx : e.map α ≫ x' = x) (hy : y ≫ d.map β = y') :
    productArrow e d (balanceNativeLeft e d x x' u y y' α β hx hy) ≫
      balance e d P' Q' x' u y' =
    balance e d P Q x u y ≫
      productArrow e d (balanceNativeRight e d x x' u y y' α β hx hy) := by
  apply Factorization.Hom.ext
  · change α ≫ 𝟙 _ = 𝟙 _ ≫ α; simp
  · change 𝟙 _ ≫ u = u ≫ 𝟙 _; simp
  · change β ≫ 𝟙 _ = 𝟙 _ ≫ β; simp

noncomputable def restrict (F : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F) : Cocone e d (D := D) where
  obj := F.obj
  map f := F.map (productArrow e d f)
  map_id s := by rw [productArrow_id, F.map_id]
  map_comp f g := by rw [productArrow_comp, F.map_comp]
  bal {Z Z' P Q} x u y := by
    let b : Primitive.Data e d := ⟨P,Q,Z,Z',x,u,y⟩
    have : IsIso (F.map (Primitive.arrow e d b)) := hF _ (MorphismProperty.ofHoms.mk b)
    exact asIso (F.map (Primitive.arrow e d b))
  bal_id x y := by
    change F.map (balance e d _ _ x _ y) = _
    rw [balance_unit_arrow]
  bal_comp x u v y := by
    change F.map (balance e d _ _ x (u ≫ v) y) = _
    rw [balance_comp_arrow, F.map_comp, F.map_comp, F.map_comp]
    rfl
  bal_natural x x' u y y' α β hx hy := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (balance_natural_arrow e d x x' u y y' α β hx hy)

/-- Restriction acts on transformations without requiring invertible components. -/
def restrictTransformation (F G : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F)
    (hG : (Primitive.generators e d).IsInvertedBy G) (a : F ⟶ G) :
    restrict e d F hF ⟶ restrict e d G hG where
  app := a.app
  native_naturality f := a.naturality (productArrow e d f)
  balance_naturality x u y := a.naturality (balance e d _ _ x u y)


def outputProduct {s t : Object e d} (f : s ⟶ t) :
    ProductHom e d s (Primitive.afterOutput e d f) :=
  ⟨𝟙 _, f.right, rfl, by simp [Primitive.afterOutput],
    by simpa [Primitive.afterOutput] using f.second_square⟩
def inputProduct {s t : Object e d} (f : s ⟶ t) :
    ProductHom e d (Primitive.afterBalance e d f) t :=
  ⟨f.left, 𝟙 _, rfl, by simpa [Primitive.afterBalance] using f.first_square,
    by change (𝟙 _) ≫ t.second = t.second ≫ d.map (𝟙 _); simp⟩

@[simp] theorem productArrow_output {s t : Object e d} (f : s ⟶ t) :
    productArrow e d (outputProduct e d f) = Primitive.outputUpdate e d f := rfl
@[simp] theorem productArrow_input {s t : Object e d} (f : s ⟶ t) :
    productArrow e d (inputProduct e d f) = Primitive.inputUpdate e d f := rfl

/-- Reverse comparison on transformations; all factorization arrows are covered. -/
def extendTransformation (F G : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F)
    (hG : (Primitive.generators e d).IsInvertedBy G)
    (a : restrict e d F hF ⟶ restrict e d G hG) : F ⟶ G :=
  Primitive.transformationOfGenerators e d F G a.app
    (fun f => a.native_naturality (outputProduct e d f))
    (fun f => a.native_naturality (inputProduct e d f))
    (fun b => a.balance_naturality b.x b.u b.y)

@[simp] theorem extend_restrict (F G : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F)
    (hG : (Primitive.generators e d).IsInvertedBy G) (a : F ⟶ G) :
    extendTransformation e d F G hF hG (restrictTransformation e d F G hF hG a) = a := by
  apply NatTrans.ext; rfl
@[simp] theorem restrict_extend (F G : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F)
    (hG : (Primitive.generators e d).IsInvertedBy G)
    (a : restrict e d F hF ⟶ restrict e d G hG) :
    restrictTransformation e d F G hF hG (extendTransformation e d F G hF hG a) = a := by
  apply Transformation.ext; rfl

/-- Exact bijection of natural transformations; not yet object essential surjectivity. -/
def transformationEquiv (F G : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F)
    (hG : (Primitive.generators e d).IsInvertedBy G) :
    (F ⟶ G) ≃ (restrict e d F hF ⟶ restrict e d G hG) where
  toFun := restrictTransformation e d F G hF hG
  invFun := extendTransformation e d F G hF hG
  left_inv := extend_restrict e d F G hF hG
  right_inv := restrict_extend e d F G hF hG


/-- The literal source product indexing category at a middle object. -/
abbrev Fibre (Z : C) := CostructuredArrow e Z × StructuredArrow Z d

def fibreObject {Z : C} (s : Fibre e d Z) : Object e d :=
  ⟨Z, s.1.left, s.2.right, s.1.hom, s.2.hom⟩
def fibreProduct {Z : C} {s t : Fibre e d Z} (f : s ⟶ t) :
    ProductHom e d (fibreObject e d s) (fibreObject e d t) :=
  native e d s.1.hom t.1.hom s.2.hom t.2.hom f.1.left f.2.right
    (CostructuredArrow.w f.1) (StructuredArrow.w f.2)

/-- Source product functors are recovered from independently declared cocone data. -/
def fibreFunctor (S : Cocone e d (D := D)) (Z : C) : Fibre e d Z ⥤ D where
  obj s := S.obj (fibreObject e d s)
  map f := S.map (fibreProduct e d f)
  map_id s := by
    have h : fibreProduct e d (𝟙 s) = productId e d (fibreObject e d s) := by
      apply ProductHom.ext <;> rfl
    rw [h, S.map_id]
  map_comp f g := by
    have h : fibreProduct e d (f ≫ g) = productComp e d (fibreProduct e d f) (fibreProduct e d g) := by
      apply ProductHom.ext <;> rfl
    rw [h, S.map_comp]

/-- Domain of a source balance natural isomorphism: left at Z, right at Z'. -/
abbrev BalanceDomain (Z Z' : C) := CostructuredArrow e Z × StructuredArrow Z' d

def balanceSourceFunctor (S : Cocone e d (D := D)) {Z Z' : C} (u : Z ⟶ Z') :
    BalanceDomain e d Z Z' ⥤ D :=
  ((𝟭 (CostructuredArrow e Z)).prod (StructuredArrow.map u)) ⋙ fibreFunctor e d S Z

def balanceTargetFunctor (S : Cocone e d (D := D)) {Z Z' : C} (u : Z ⟶ Z') :
    BalanceDomain e d Z Z' ⥤ D :=
  ((CostructuredArrow.map u).prod (𝟭 (StructuredArrow Z' d))) ⋙ fibreFunctor e d S Z'

/-- The independent balance data form an actual natural isomorphism between
source product functors, not merely objectwise invertible maps. -/
def balanceNaturalIso (S : Cocone e d (D := D)) {Z Z' : C} (u : Z ⟶ Z') :
    balanceSourceFunctor e d S u ≅ balanceTargetFunctor e d S u :=
  NatIso.ofComponents (fun s => S.bal s.1.hom u s.2.hom) (by
    intro s t f
    exact S.bal_natural s.1.hom t.1.hom u s.2.hom t.2.hom f.1.left f.2.right
      (CostructuredArrow.w f.1) (StructuredArrow.w f.2))


/-- Comparison from primitive-inverting functors into independent source cocones. -/
noncomputable def restrictionFunctor :
    (Primitive.generators e d).FunctorsInverting D ⥤ Cocone e d (D := D) where
  obj F := restrict e d F.obj F.property
  map {F G} a := restrictTransformation e d F.obj G.obj F.property G.property a.hom
  map_id F := by apply Transformation.ext; rfl
  map_comp a b := by apply Transformation.ext; rfl

/-- Full faithfulness is established; essential surjectivity is not assumed. -/
noncomputable def restrictionFullyFaithful :
    (restrictionFunctor e d (D := D)).FullyFaithful where
  preimage {F G} a := ⟨extendTransformation e d F.obj G.obj F.property G.property a⟩
  map_preimage a := restrict_extend e d _ _ _ _ a
  preimage_map a := by
    apply InducedCategory.Hom.ext
    exact extend_restrict e d _ _ _ _ a.hom


set_option backward.isDefEq.respectTransparency false in
/-- At each fixed middle index, the product-arrow interface is exactly the
literal product of costructured and structured arrow categories. -/
def fibreHomEquiv {Z : C} (s t : Fibre e d Z) :
    (s ⟶ t) ≃ ProductHom e d (fibreObject e d s) (fibreObject e d t) where
  toFun := fibreProduct e d
  invFun f :=
    ⟨CostructuredArrow.homMk f.left (by simpa [fibreObject] using f.first_square),
      StructuredArrow.homMk f.right (by
        have h := f.second_square
        change (𝟙 Z) ≫ t.2.hom = s.2.hom ≫ d.map f.right at h
        simpa using h.symm)⟩
  left_inv f := by
    apply CategoryTheory.Prod.hom_ext
    · apply Comma.hom_ext <;> rfl
    · apply Comma.hom_ext <;> rfl
  right_inv f := by apply ProductHom.ext <;> rfl


/-- Candidate action on a general factorization arrow, built only from the
independent product and balance data. Its functor laws remain a separate obligation. -/
def extensionMap (S : Cocone e d (D := D)) {s t : Object e d} (f : s ⟶ t) :
    S.obj s ⟶ S.obj t :=
  S.map (outputProduct e d f) ≫ (S.bal s.first f.middle t.second).hom ≫
    S.map (inputProduct e d f)

/-- The candidate extension agrees with the original functor on restricted data. -/
theorem extensionMap_restrict (F : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F) {s t : Object e d} (f : s ⟶ t) :
    extensionMap e d (restrict e d F hF) f = F.map f := by
  change F.map (Primitive.outputUpdate e d f) ≫ F.map (balance e d _ _ _ _ _) ≫
    F.map (Primitive.inputUpdate e d f) = F.map f
  dsimp only [Primitive.outputUpdate, Primitive.inputUpdate, Primitive.afterOutput, Primitive.afterBalance]
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  exact (Category.assoc _ _ _).symm.trans (Primitive.arrow_decomposition e d f)

end ContextualComposition.Factorization.Source
