module
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-! At the empty input, admitted families have no components and no body points. The comma hom recovers the entire content fibre, including its noninvertible arrows. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.EmptyInterfaceHom
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

universe u w v wL vL wN vN
variable {G : Type w} [Category.{v} G] (raw : G ⥤ Type u) (J : MorphismProperty (Type u))
abbrev Zero := PEmpty.{u+1}
def total (P : Zero.{u} → G) := Σ i, raw.obj (P i)
def projection (P : Zero.{u} → G) : total raw P ⟶ Zero := TypeCat.ofHom Sigma.fst

structure Context where
  grade : Zero.{u} → G
  admitted : J (projection raw grade)

instance : Category (Context raw J) where
  Hom P Q := ∀ i, P.grade i ⟶ Q.grade i
  id _ _ := 𝟙 _
  comp f g i := f i ≫ g i
  id_comp _ := funext fun i => i.elim
  comp_id _ := funext fun i => i.elim
  assoc _ _ _ := funext fun i => i.elim

instance (P Q : Context raw J) : Unique (P ⟶ Q) where
  default := fun i => i.elim
  uniq _ := funext fun i => i.elim

def extension : Context raw J ⥤ Type u where
  obj P := total raw P.grade
  map f := TypeCat.ofHom fun s => ⟨s.1,raw.map (f s.1) s.2⟩
  map_id _ := by apply ConcreteCategory.hom_ext; intro s; exact s.1.elim
  map_comp _ _ := by apply ConcreteCategory.hom_ext; intro s; exact s.1.elim

/-- Every empty-index family projection is an isomorphism, so only the usual admission of isomorphisms is needed. -/
def projectionIso (P : Zero.{u} → G) : total raw P ≅ Zero where
  hom := projection raw P
  inv := TypeCat.ofHom PEmpty.elim
  hom_inv_id := by apply ConcreteCategory.hom_ext; intro s; exact s.1.elim
  inv_hom_id := by apply ConcreteCategory.hom_ext; intro i; exact i.elim

variable (admitIso : ∀ {X Y : Type u} (e : X ≅ Y), J e.hom)
def emptyContext : Context raw J := ⟨PEmpty.elim,admitIso (projectionIso raw PEmpty.elim)⟩

variable {L : Type wL} [Category.{vL} L] (d : L ⥤ Type u)
abbrev Mixed := Comma (extension raw J) d

def sectionFunctor : L ⥤ Mixed raw J d where
  obj Q := ⟨emptyContext raw J admitIso,Q,TypeCat.ofHom (fun s => s.1.elim)⟩
  map f := ⟨𝟙 _,f,by apply ConcreteCategory.hom_ext; intro s; exact s.1.elim⟩
  map_id _ := Comma.hom_ext _ _ (Subsingleton.elim _ _) rfl
  map_comp _ _ := Comma.hom_ext _ _ (Subsingleton.elim _ _) rfl

def equivalence : Mixed raw J d ≌ L where
  functor := Comma.snd _ _
  inverse := sectionFunctor raw J admitIso d
  unitIso := NatIso.ofComponents (fun X =>
    Comma.isoMk (⟨default,default,Subsingleton.elim _ _,Subsingleton.elim _ _⟩ :
      X.left ≅ emptyContext raw J admitIso) (Iso.refl _)
      (by apply ConcreteCategory.hom_ext; intro s; exact s.1.elim))
    (by intro X Y f; exact Comma.hom_ext _ _ (Subsingleton.elim _ _) (by simp [sectionFunctor]))
  counitIso := Iso.refl _

variable {N : Type wN} [Category.{vN} N] (d' : N ⥤ Type u) (t : L ⥤ N) (a : d ⟶ t ⋙ d')

/-- Covariant pure transport on the comma presentation, using its original extension map. -/
def post : Mixed raw J d ⥤ Mixed raw J d' where
  obj X := ⟨X.left,t.obj X.right,X.hom ≫ a.app X.right⟩
  map {X Y} f := ⟨f.left,t.map f.right,by
    rw [← Category.assoc,f.w,Category.assoc,a.naturality,Category.assoc]; rfl⟩

theorem post_projection : post raw J d d' t a ⋙ Comma.snd _ _ = Comma.snd _ _ ⋙ t := rfl

include admitIso in
theorem post_equivalence_iff : (post raw J d d' t a).IsEquivalence ↔ t.IsEquivalence := by
  let E := equivalence raw J admitIso d
  let E' := equivalence raw J admitIso d'
  let _ : (Comma.snd (extension raw J) d).IsEquivalence := E.isEquivalence_functor
  let _ : (Comma.snd (extension raw J) d').IsEquivalence := E'.isEquivalence_functor
  constructor
  · intro h
    let := h
    have prod : (post raw J d d' t a ⋙ Comma.snd _ _).IsEquivalence := inferInstance
    rw [post_projection] at prod
    exact Functor.isEquivalence_of_comp_left (Comma.snd (extension raw J) d) t
  · intro h
    let := h
    have prod : (Comma.snd (extension raw J) d ⋙ t).IsEquivalence := inferInstance
    rw [← post_projection raw J d d' t a] at prod
    exact Functor.isEquivalence_of_comp_right (post raw J d d' t a) (Comma.snd (extension raw J) d')

end ContextualComposition.EmptyInterfaceHom
