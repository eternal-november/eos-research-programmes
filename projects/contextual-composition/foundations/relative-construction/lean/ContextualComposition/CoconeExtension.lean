module
public import ContextualComposition.SourceCocone
@[expose] public section
namespace ContextualComposition.Factorization.Source
open CategoryTheory CategoryTheory.Functor
universe vK vL vC vD uK uL uC uD
variable {K : Type uK} {L : Type uL} {C : Type uC} {D : Type uD}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C] [Category.{vD} D]
variable (e : K ⥤ C) (d : L ⥤ C)

/-- The output update commuted to the left of the first balance. -/
def beforeBalance {s t r : Object e d} (f : s ⟶ t) (g : t ⟶ r) :=
  balanceNativeLeft e d s.first s.first f.middle t.second (g.middle ≫ r.second)
    (𝟙 s.left) g.right (by simp) g.second_square.symm
/-- Output update in the common intermediate fibre. -/
def middleOutput {s t r : Object e d} (f : s ⟶ t) (g : t ⟶ r) :=
  balanceNativeRight e d s.first s.first f.middle t.second (g.middle ≫ r.second)
    (𝟙 s.left) g.right (by simp) g.second_square.symm
/-- Input update in that same intermediate fibre. -/
def middleInput {s t r : Object e d} (f : s ⟶ t) (g : t ⟶ r) :=
  balanceNativeLeft e d (s.first ≫ f.middle) t.first g.middle r.second r.second
    f.left (𝟙 r.right) f.first_square (by simp)
/-- Input update commuted to the right of the second balance. -/
def afterBalance {s t r : Object e d} (f : s ⟶ t) (g : t ⟶ r) :=
  balanceNativeRight e d (s.first ≫ f.middle) t.first g.middle r.second r.second
    f.left (𝟙 r.right) f.first_square (by simp)

variable (S : Cocone e d (D := D))
theorem extensionMap_id (s : Object e d) : extensionMap e d S (𝟙 s) = 𝟙 (S.obj s) := by
  change S.map (outputProduct e d (𝟙 s)) ≫ (S.bal s.first (𝟙 _) s.second).hom ≫
    S.map (inputProduct e d (𝟙 s)) = _
  rw [S.bal_id]
  have h : productComp e d (outputProduct e d (𝟙 s))
      (productComp e d (balanceUnit e d s.first s.second) (inputProduct e d (𝟙 s))) =
      productId e d s := by
        apply ProductHom.ext
        · change (𝟙 s.left) ≫ (𝟙 s.left) ≫ (𝟙 s.left) = 𝟙 s.left
          simp
        · change (𝟙 s.right) ≫ (𝟙 s.right) ≫ (𝟙 s.right) = 𝟙 s.right
          simp
  calc
    _ = S.map (productComp e d (outputProduct e d (𝟙 s))
      (productComp e d (balanceUnit e d s.first s.second) (inputProduct e d (𝟙 s)))) := by
        dsimp only [outputProduct, inputProduct, Primitive.afterOutput, Primitive.afterBalance, category]
        rw [S.map_comp, S.map_comp]
    _ = _ := by rw [h, S.map_id]


theorem extensionMap_comp {s t r : Object e d} (f : s ⟶ t) (g : t ⟶ r) :
    extensionMap e d S (f ≫ g) = extensionMap e d S f ≫ extensionMap e d S g := by
  let al := balanceAssocLeft e d s.first f.middle g.middle r.second
  let ar := balanceAssocRight e d s.first f.middle g.middle r.second
  have hL : S.map (outputProduct e d (f ≫ g)) ≫ S.map al =
      S.map (outputProduct e d f) ≫ S.map (beforeBalance e d f g) := by
    dsimp only [al, outputProduct, Primitive.afterOutput, beforeBalance, balanceNativeLeft]
    rw [← S.map_comp, ← S.map_comp]
    congr 1
    apply ProductHom.ext
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
    · change (f.right ≫ g.right) ≫ 𝟙 _ = f.right ≫ g.right; simp
  have hR : S.map ar ≫ S.map (inputProduct e d (f ≫ g)) =
      S.map (afterBalance e d f g) ≫ S.map (inputProduct e d g) := by
    dsimp only [ar, inputProduct, Primitive.afterBalance, afterBalance, balanceNativeRight]
    rw [← S.map_comp, ← S.map_comp]
    congr 1
    apply ProductHom.ext
    · change 𝟙 _ ≫ (f.left ≫ g.left) = f.left ≫ g.left; simp
    · change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
  have hM : S.map (inputProduct e d f) ≫ S.map (outputProduct e d g) =
      S.map (middleOutput e d f g) ≫ S.map (middleInput e d f g) := by
    dsimp only [inputProduct, outputProduct, Primitive.afterBalance, Primitive.afterOutput,
      middleOutput, middleInput, balanceNativeRight, balanceNativeLeft]
    rw [← S.map_comp, ← S.map_comp]
    congr 1
    apply ProductHom.ext
    · change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left; simp
    · change 𝟙 _ ≫ g.right = g.right ≫ 𝟙 _; simp
  have hN₁ : S.map (beforeBalance e d f g) ≫ (S.bal s.first f.middle (g.middle ≫ r.second)).hom =
      (S.bal s.first f.middle t.second).hom ≫ S.map (middleOutput e d f g) :=
    S.bal_natural s.first s.first f.middle t.second (g.middle ≫ r.second)
      (𝟙 s.left) g.right (by simp) g.second_square.symm
  have hN₂ : S.map (middleInput e d f g) ≫ (S.bal t.first g.middle r.second).hom =
      (S.bal (s.first ≫ f.middle) g.middle r.second).hom ≫ S.map (afterBalance e d f g) :=
    S.bal_natural (s.first ≫ f.middle) t.first g.middle r.second r.second
      f.left (𝟙 r.right) f.first_square (by simp)
  change S.map (outputProduct e d (f ≫ g)) ≫
      (S.bal s.first (f.middle ≫ g.middle) r.second).hom ≫
      S.map (inputProduct e d (f ≫ g)) = _
  rw [S.bal_comp]
  change S.map (outputProduct e d (f ≫ g)) ≫
      (S.map al ≫ (S.bal s.first f.middle (g.middle ≫ r.second)).hom ≫
        (S.bal (s.first ≫ f.middle) g.middle r.second).hom ≫ S.map ar) ≫
      S.map (inputProduct e d (f ≫ g)) = _
  simp only [Category.assoc]
  rw [← Category.assoc, hL]
  simp only [Category.assoc]
  rw [hR]
  dsimp only [outputProduct, inputProduct, Primitive.afterOutput, Primitive.afterBalance] at *
  rw [← Category.assoc (S.map (beforeBalance e d f g)), hN₁]
  simp only [Category.assoc]
  rw [← Category.assoc (S.bal (s.first ≫ f.middle) g.middle r.second).hom, ← hN₂]
  simp only [Category.assoc]
  rw [← Category.assoc (S.map (middleOutput e d f g)), ← hM]
  simp only [extensionMap, outputProduct, inputProduct, Primitive.afterOutput, Primitive.afterBalance, Category.assoc]


/-- Extension uses only independently supplied source relations. -/
def extensionFunctor : Object e d ⥤ D where
  obj := S.obj
  map := extensionMap e d S
  map_id := extensionMap_id e d S
  map_comp := extensionMap_comp e d S

theorem extensionMap_product {s t : Object e d} (f : ProductHom e d s t) :
    extensionMap e d S (productArrow e d f) = S.map f := by
  rcases s with ⟨Z,P,Q,x,y⟩
  rcases t with ⟨Z',P',Q',x',y'⟩
  rcases f with ⟨α,β,h,hx,hy⟩
  dsimp at h
  subst Z'
  let f : ProductHom e d ⟨Z,P,Q,x,y⟩ ⟨Z,P',Q',x',y'⟩ := ⟨α,β,rfl,hx,hy⟩
  change S.map (outputProduct e d (productArrow e d f)) ≫
    (S.bal x (𝟙 Z) y').hom ≫ S.map (inputProduct e d (productArrow e d f)) = S.map f
  rw [S.bal_id]
  have hcomp : productComp e d (outputProduct e d (productArrow e d f))
      (productComp e d (balanceUnit e d x y') (inputProduct e d (productArrow e d f))) = f := by
    apply ProductHom.ext
    · change 𝟙 _ ≫ 𝟙 _ ≫ α = α; simp
    · change β ≫ 𝟙 _ ≫ 𝟙 _ = β; simp
  calc
    _ = S.map (productComp e d (outputProduct e d (productArrow e d f))
      (productComp e d (balanceUnit e d x y') (inputProduct e d (productArrow e d f)))) := by
        exact ((S.map_comp (outputProduct e d (productArrow e d f))
          (productComp e d (balanceUnit e d x y') (inputProduct e d (productArrow e d f)))).trans
          (congrArg (fun k => S.map (outputProduct e d (productArrow e d f)) ≫ k)
            (S.map_comp (balanceUnit e d x y') (inputProduct e d (productArrow e d f))))).symm
    _ = _ := congrArg S.map hcomp

theorem extensionMap_balance {Z Z' : C} {P : K} {Q : L}
    (x : e.obj P ⟶ Z) (u : Z ⟶ Z') (y : Z' ⟶ d.obj Q) :
    extensionMap e d S (balance e d P Q x u y) = (S.bal x u y).hom := by
  have ho : outputProduct e d (balance e d P Q x u y) = productId e d ⟨Z,P,Q,x,u ≫ y⟩ := by
    apply ProductHom.ext <;> rfl
  have hi : inputProduct e d (balance e d P Q x u y) = productId e d ⟨Z',P,Q,x ≫ u,y⟩ := by
    apply ProductHom.ext <;> rfl
  change S.map (outputProduct e d (balance e d P Q x u y)) ≫
    (S.bal x u y).hom ≫ S.map (inputProduct e d (balance e d P Q x u y)) = _
  rw [ho, hi]
  dsimp only [Primitive.afterOutput, Primitive.afterBalance, balance]
  rw [S.map_id, S.map_id, Category.id_comp, Category.comp_id]

theorem extension_inverts : (Primitive.generators e d).IsInvertedBy (extensionFunctor e d S) := by
  intro s t f hf
  cases hf with
  | mk b =>
    change IsIso (extensionMap e d S (balance e d b.P b.Q b.x b.u b.y))
    rw [extensionMap_balance]
    infer_instance


/-- Explicit object-level inverse comparison, with identity components. -/
noncomputable def restrictionExtensionIso :
    restrict e d (extensionFunctor e d S) (extension_inverts e d S) ≅ S where
  hom :=
    { app := fun _ => 𝟙 _
      native_naturality := by
        intro s t f
        change extensionMap e d S (productArrow e d f) ≫ 𝟙 _ = 𝟙 _ ≫ S.map f
        rw [Category.comp_id, Category.id_comp, extensionMap_product]
      balance_naturality := by
        intro Z Z' P Q x u y
        change extensionMap e d S (balance e d P Q x u y) ≫ 𝟙 _ = 𝟙 _ ≫ (S.bal x u y).hom
        rw [Category.comp_id, Category.id_comp, extensionMap_balance] }
  inv :=
    { app := fun _ => 𝟙 _
      native_naturality := by
        intro s t f
        change S.map f ≫ 𝟙 _ = 𝟙 _ ≫ extensionMap e d S (productArrow e d f)
        rw [Category.comp_id, Category.id_comp, extensionMap_product]
      balance_naturality := by
        intro Z Z' P Q x u y
        change (S.bal x u y).hom ≫ 𝟙 _ = 𝟙 _ ≫ extensionMap e d S (balance e d P Q x u y)
        rw [Category.comp_id, Category.id_comp, extensionMap_balance] }
  hom_inv_id := by apply Transformation.ext; funext s; exact Category.id_comp _
  inv_hom_id := by apply Transformation.ext; funext s; exact Category.id_comp _

/-- The explicit extension also recovers every original primitive-inverting functor. -/
noncomputable def extensionRestrictionIso (F : Object e d ⥤ D)
    (hF : (Primitive.generators e d).IsInvertedBy F) :
    extensionFunctor e d (restrict e d F hF) ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro s t f
    change extensionMap e d (restrict e d F hF) f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    rw [Category.comp_id, Category.id_comp, extensionMap_restrict])

variable (D)
/-- Every independently specified cocone has an actual primitive-inverting extension. -/
theorem restrictionEssSurj : (restrictionFunctor e d (D := D)).EssSurj where
  mem_essImage S := ⟨⟨extensionFunctor e d S, extension_inverts e d S⟩,
    ⟨restrictionExtensionIso e d S⟩⟩

/-- Full fixed-target source-presentation comparison, on objects and transformations. -/
noncomputable def presentationEquivalence :
    (Primitive.generators e d).FunctorsInverting D ≌ Cocone e d (D := D) := by
  letI := (restrictionFullyFaithful e d (D := D)).full
  letI := (restrictionFullyFaithful e d (D := D)).faithful
  letI := restrictionEssSurj (D := D) e d
  letI : (restrictionFunctor e d (D := D)).IsEquivalence := {}
  exact (restrictionFunctor e d (D := D)).asEquivalence

/-- Pseudobalanced cocones at fixed e,d,D are equivalent to comma functors. -/
noncomputable def commaCoconeEquivalence :
    (Comma e d ⥤ D) ≌ Cocone e d (D := D) :=
  (Primitive.universalProperty e d D).trans (presentationEquivalence (D := D) e d)

end ContextualComposition.Factorization.Source
