module
public import ContextualComposition.RepresentablePureAssocCastFrame
public import ContextualComposition.RepresentablePureBuilder
public import ContextualComposition.RepresentableKleisliBicategory
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureGenericAssembly
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Pseudofunctor
open RepresentableBicategoryAssembly RepresentableKleisliBicategory RepresentableKleisliGeneric
open RepresentablePureAssociativity RepresentablePureCastTranslation
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false

universe u v w s
structure Core (B : Type s) where
  as : B

variable {C : Type u} [Bicategory.{w,v} C] [Bicategory.Strict C] {B : Type s}
variable (X : B → C)
@[instance_reducible]
def coreCategory : Category (Core B) where
  Hom a b := X a.as ⟶ X b.as
  id _ := 𝟙 _
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

variable (F : StrictPseudofunctor C C) (μ : (X : C) → F.obj (F.obj X) ⟶ F.obj X)
variable (e : ∀ X : C, X ⟶ F.obj X)
variable (L : ∀ {a b : C} (f : a ⟶ F.obj b), RepresentableKleisliGeneric.cmp F μ (e a) f ≅ f)
abbrev KH (a b : Part B) := X a.as ⟶ F.obj (X b.as)

def multiply {a b c : Part B} : KH X F a b × KH X F b c ⥤ KH X F a c where
  obj x := RepresentableKleisliGeneric.cmp F μ x.1 x.2
  map t := cell F μ t.1 t.2
  map_id x := by
    change RepresentableKleisli.horizontal (𝟙 _) (F.map₂ (𝟙 _)) ▷ μ (X c.as) = _
    rw [F.map₂_id,RepresentableKleisli.horizontal_id,id_whiskerRight]
    rfl
  map_comp t q := by
    change RepresentableKleisli.horizontal (_ ≫ _) (F.map₂ (_ ≫ _)) ▷ μ (X c.as) = _
    rw [F.map₂_comp,RepresentableKleisli.horizontal_comp,comp_whiskerRight]
    rfl

abbrev Left := ∀ {a b : B} (f : X a ⟶ F.obj (X b)), RepresentableKleisliGeneric.cmp F μ (e (X a)) f ≅ f
abbrev Right := ∀ {a b : B} (f : X a ⟶ F.obj (X b)), RepresentableKleisliGeneric.cmp F μ f (e (X b)) ≅ f
abbrev Assoc := ∀ {a b c d : B} (f : X a ⟶ F.obj (X b)) (g : X b ⟶ F.obj (X c)) (h : X c ⟶ F.obj (X d)),
    RepresentableKleisliGeneric.cmp F μ (RepresentableKleisliGeneric.cmp F μ f g) h ≅
    RepresentableKleisliGeneric.cmp F μ f (RepresentableKleisliGeneric.cmp F μ g h)

variable (l : Left X F μ e) (r : Right X F μ e) (a : Assoc X F μ)

def ops : Operations (KH X F) where
  unit x := e (X x.as)
  multiply := multiply X F μ
  left {_ _} f := l f
  right {_ _} f := r f
  assoc {_ _ _ _} f g h := a f g h

structure RawFaces : Prop where
  association : ∀ {x y z r : B} (f : X x ⟶ X y) (g : X y ⟶ X z) (h : X z ⟶ X r),
    a (J F e f) (J F e g) (J F e h) ≪≫ ws F μ (J F e f) (c F μ e L g h) ≪≫ c F μ e L f (g ≫ h) =
      wr F μ (c F μ e L f g) (J F e h) ≪≫ c F μ e L (f ≫ g) h ≪≫ whiskerRightIso (α_ f g h) (e (X r))
  left : ∀ {x y : B} (f : X x ⟶ X y),
    c F μ e L (𝟙 (X x)) f ≪≫ whiskerRightIso (λ_ f) (e (X y)) =
      wr F μ (λ_ (e (X x))) (J F e f) ≪≫ l (J F e f)
  right : ∀ {x y : B} (f : X x ⟶ X y),
    c F μ e L f (𝟙 (X y)) ≪≫ whiskerRightIso (ρ_ f) (e (X y)) =
      ws F μ (J F e f) (λ_ (e (X y))) ≪≫ r (J F e f)

def faces (R : RawFaces X F μ e L l r a) :
    letI : Category (Core B) := coreCategory X
    RepresentablePureBuilder.Faces (A := Core B) (ops X F μ e l r a) := by
  letI : Category (Core B) := coreCategory X
  refine {
    obj := fun x => ⟨x.as⟩
    map := fun f => J F e f
    unit := fun x => λ_ (e (X x.as))
    comp := fun f g => c F μ e L f g
    assoc := ?_, left := ?_, right := ?_ }
  · intro x y z j f g h
    exact RepresentablePureAssocCastFrame.cast F μ e L f g h
      (a (J F e f) (J F e g) (J F e h)) (R.association f g h)
  · intro x y f
    exact unital (c F μ e L (𝟙 (X x.as)) f) (whiskerRightIso (λ_ f) (e (X y.as)))
      (wr F μ (λ_ (e (X x.as))) (J F e f)) (l (J F e f)) _ _
      (first F μ (λ_ (e (X x.as))).hom (J F e f)).symm (leftTail f (e (X y.as))) (R.left f)
  · intro x y f
    exact unital (c F μ e L f (𝟙 (X y.as))) (whiskerRightIso (ρ_ f) (e (X y.as)))
      (ws F μ (J F e f) (λ_ (e (X y.as)))) (r (J F e f)) _ _
      (second F μ (J F e f) (λ_ (e (X y.as))).hom).symm (rightTail f (e (X y.as))) (R.right f)

end ContextualComposition.GrothendieckStep.RepresentablePureGenericAssembly
