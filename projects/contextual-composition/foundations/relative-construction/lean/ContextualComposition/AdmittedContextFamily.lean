module
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! Interface-indexed families with an admitted total projection. Reindexing along an arbitrary set map only pulls back the already admitted family projection. -/

@[expose] public section
namespace ContextualComposition.AdmittedContextFamily
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
universe u w v
variable {G : Type w} [Category.{v} G] (raw : G ⥤ Type u) (J : MorphismProperty (Type u))
variable {A B D : Type u}

def extent (p : A → G) := Σ i, raw.obj (p i)
def projection (p : A → G) : extent raw p ⟶ A := TypeCat.ofHom Sigma.fst

structure Family (A : Type u) where
  grade : A → G
  admitted : J (projection raw grade)

instance (A : Type u) : Category.{max u v} (Family raw J A) where
  Hom P Q := ∀ i, P.grade i ⟶ Q.grade i
  id _ _ := 𝟙 _
  comp f g i := f i ≫ g i
  id_comp f := funext fun i => Category.id_comp (f i)
  comp_id f := funext fun i => Category.comp_id (f i)
  assoc f g h := funext fun i => Category.assoc (f i) (g i) (h i)

def extension (A : Type u) : Family raw J A ⥤ Type u where
  obj P := extent raw P.grade
  map f := TypeCat.ofHom fun s => ⟨s.1,raw.map (f s.1) s.2⟩
  map_id P := by
    apply ConcreteCategory.hom_ext; rintro ⟨i,x⟩
    change (Sigma.mk i (raw.map (𝟙 (P.grade i)) x) : extent raw P.grade) = _
    rw [raw.map_id]; rfl
  map_comp {P Q R} f g := by
    apply ConcreteCategory.hom_ext; rintro ⟨i,x⟩
    change (Sigma.mk i (raw.map (f i ≫ g i) x) : extent raw R.grade) = _
    rw [raw.map_comp]; rfl

def extendMap (p : B → G) (a : A ⟶ B) : extent raw (fun x => p (a x)) ⟶ extent raw p :=
  TypeCat.ofHom fun s => ⟨a s.1,s.2⟩

theorem extension_pullback (p : B → G) (a : A ⟶ B) :
    IsPullback (extendMap raw p a) (projection raw (fun x => p (a x))) (projection raw p) a := by
  apply (Types.isPullback_iff ..).mpr
  refine ⟨rfl,?_,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ ⟨h,k⟩
    change i = j at k
    subst j
    change (Sigma.mk (a i) x : extent raw p) = Sigma.mk (a i) y at h
    exact congrArg (fun z => (Sigma.mk i z : extent raw (fun i => p (a i)))) (eq_of_heq (Sigma.mk.inj h).2)
  · rintro ⟨b,x⟩ a' h
    change b = a a' at h
    subst b
    exact ⟨⟨a',x⟩,rfl,rfl⟩

variable [J.IsStableUnderBaseChange]
def pull (a : A ⟶ B) : Family raw J B ⥤ Family raw J A where
  obj P := ⟨fun i => P.grade (a i),J.of_isPullback (extension_pullback raw P.grade a) P.admitted⟩
  map f := fun i => f (a i)
  map_id _ := rfl
  map_comp _ _ := rfl

def pullExtension (a : A ⟶ B) : pull raw J a ⋙ extension raw J A ⟶ extension raw J B where
  app P := extendMap raw P.grade a
  naturality _ _ _ := rfl

theorem pull_id (A : Type u) : pull raw J (𝟙 A) = 𝟭 (Family raw J A) := rfl
theorem pull_comp (a : A ⟶ B) (b : B ⟶ D) : pull raw J (a ≫ b) = pull raw J b ⋙ pull raw J a := rfl

end ContextualComposition.AdmittedContextFamily
