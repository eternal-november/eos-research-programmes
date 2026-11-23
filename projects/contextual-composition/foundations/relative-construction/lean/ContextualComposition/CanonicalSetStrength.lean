module
public import Mathlib.CategoryTheory.Types.Basic

/-! Set endofunctors carry the slice-insertion strength used in the constantized content presentation. Every natural transformation respects it, including noninvertible grade, arity, unit and multiplication maps. -/

@[expose] public section
namespace ContextualComposition.CanonicalSetStrength
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y Z A B : Type u}
def frame (X : Type u) : Type u ⥤ Type u where
  obj A := X × A
  map f := TypeCat.ofHom (Prod.map id (fun a => f a))
  map_id _ := rfl
  map_comp _ _ := rfl

def insert (x : X) (A : Type u) : A ⟶ X × A := TypeCat.ofHom (Prod.mk x)
def reparam (q : X → Y) : frame X ⟶ frame Y where
  app _ := TypeCat.ofHom (Prod.map q id)
  naturality _ _ _ := rfl

theorem reparam_id : reparam (id : X → X) = 𝟙 (frame X) := rfl
theorem reparam_comp (q : X → Y) (r : Y → Z) : reparam (r ∘ q) = reparam q ≫ reparam r := rfl

def unitor (A : Type u) : PUnit.{u+1} × A ≅ A := (Equiv.punitProd A).toIso

def associator (X Y A : Type u) : X × (Y × A) ≅ (X × Y) × A :=
  (Equiv.prodAssoc X Y A).symm.toIso

variable (F G : Type u ⥤ Type u)
def strength (X : Type u) : F ⋙ frame X ⟶ frame X ⋙ F where
  app A := TypeCat.ofHom (fun p => F.map (insert p.1 A) p.2)
  naturality A B f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x,z⟩
    have h : f ≫ insert x B = insert x A ≫ (frame X).map f := rfl
    exact congrArg (fun (k : F.obj A ⟶ F.obj (X × B)) => k z)
      ((F.map_comp f (insert x B)).symm.trans ((congrArg F.map h).trans (F.map_comp _ _)))

theorem parameter (q : X → Y) (A : Type u) :
    (reparam q).app (F.obj A) ≫ (strength F Y).app A =
      (strength F X).app A ≫ F.map ((reparam q).app A) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x,z⟩
  exact congrArg (fun (k : F.obj A ⟶ F.obj (Y × A)) => k z)
    (F.map_comp (insert x A) ((reparam q).app A))

theorem respects (α : F ⟶ G) (X A : Type u) :
    (frame X).map (α.app A) ≫ (strength G X).app A =
      (strength F X).app A ≫ α.app (X × A) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x,z⟩
  exact (congrArg (fun (k : F.obj A ⟶ G.obj (X × A)) => k z) (α.naturality (insert x A))).symm

theorem composite (X A : Type u) : (strength (F ⋙ G) X).app A =
    (strength G X).app (F.obj A) ≫ G.map ((strength F X).app A) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x,z⟩
  exact congrArg (fun (k : G.obj (F.obj A) ⟶ G.obj (F.obj (X × A))) => k z)
    (G.map_comp (insert x (F.obj A)) ((strength F X).app A))

theorem unit_frame (A : Type u) :
    (strength F PUnit.{u+1}).app A ≫ F.map (unitor A).hom = (unitor (F.obj A)).hom := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x,z⟩
  exact congrArg (fun (k : F.obj A ⟶ F.obj A) => k z)
    ((F.map_comp (insert x A) (unitor A).hom).symm.trans (F.map_id A))

theorem associate_frames (X Y A : Type u) :
    (frame X).map ((strength F Y).app A) ≫ (strength F X).app (Y × A) ≫ F.map (associator X Y A).hom =
      (associator X Y (F.obj A)).hom ≫ (strength F (X × Y)).app A := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x,y,z⟩
  have h : insert y A ≫ insert x (Y × A) ≫ (associator X Y A).hom = insert (x,y) A := rfl
  change (F.map (insert y A) ≫ F.map (insert x (Y × A)) ≫ F.map (associator X Y A).hom) z = F.map (insert (x,y) A) z
  simpa only [Functor.map_comp,Category.assoc] using congrArg (fun (k : A ⟶ (X × Y) × A) => F.map k z) h

end ContextualComposition.CanonicalSetStrength
