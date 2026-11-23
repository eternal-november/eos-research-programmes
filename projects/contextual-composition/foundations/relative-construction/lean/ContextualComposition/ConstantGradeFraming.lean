module
public import ContextualComposition.AdmittedContextFamily
public import ContextualComposition.CanonicalSetStrength
public import Mathlib.CategoryTheory.Comma.Basic

/-! The local part of the full Set action for constantized content grades. The context projection is reindexed by pullback; every context coefficient and every forward native content map is retained. -/

@[expose] public section
namespace ContextualComposition.ConstantGradeFraming
open CategoryTheory CanonicalSetStrength
set_option backward.isDefEq.respectTransparency false
universe u w v wL vL
variable {G : Type w} [Category.{v} G] {L : Type wL} [Category.{vL} L]
variable (raw : G ⥤ Type u) (J : MorphismProperty (Type u)) [J.IsStableUnderBaseChange]
variable (F : L ⥤ (Type u ⥤ Type u))
variable {A A' B B' : Type u}

abbrev value (B : Type u) := F ⋙ (evaluation (Type u) (Type u)).obj B
abbrev Mixed (A B : Type u) := Comma (AdmittedContextFamily.extension raw J A) (value F B)

def reindex (a : A' ⟶ A) (B : Type u) : Mixed raw J F A B ⥤ Mixed raw J F A' B where
  obj P := ⟨(AdmittedContextFamily.pull raw J a).obj P.left,P.right,
    (AdmittedContextFamily.pullExtension raw J a).app P.left ≫ P.hom⟩
  map f := ⟨(AdmittedContextFamily.pull raw J a).map f.left,f.right,by
    apply ConcreteCategory.hom_ext
    rintro ⟨i,x⟩
    exact congrArg (fun k => k (Sigma.mk (a i) x)) f.w⟩

def relabel (A : Type u) (b : B ⟶ B') : Mixed raw J F A B ⥤ Mixed raw J F A B' where
  obj P := ⟨P.left,P.right,P.hom ≫ (F.obj P.right).map b⟩
  map {P Q} f := ⟨f.left,f.right,by
    rw [← Category.assoc,f.w,Category.assoc]
    exact (congrArg (fun k => P.hom ≫ k) ((F.map f.right).naturality b).symm).trans (Category.assoc _ _ _).symm⟩

def framed (X : Type u) : Mixed raw J F A B ⥤ Mixed raw J F (X × A) (X × B) where
  obj P := ⟨(AdmittedContextFamily.pull raw J (TypeCat.ofHom Prod.snd)).obj P.left,P.right,
    TypeCat.ofHom (fun z => (F.obj P.right).map (insert z.1.1 B) (P.hom ⟨z.1.2,z.2⟩))⟩
  map {P Q} f := ⟨(AdmittedContextFamily.pull raw J (TypeCat.ofHom Prod.snd)).map f.left,f.right,by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,i⟩,w⟩
    have sq := congrArg (fun (k : AdmittedContextFamily.extent raw P.left.grade ⟶ (F.obj Q.right).obj B) => k ⟨i,w⟩) f.w
    change Q.hom ⟨i,raw.map (f.left i) w⟩ = (F.map f.right).app B (P.hom ⟨i,w⟩) at sq
    change (F.obj Q.right).map (insert x B) (Q.hom ⟨i,raw.map (f.left i) w⟩) =
      (F.map f.right).app (X × B) ((F.obj P.right).map (insert x B) (P.hom ⟨i,w⟩))
    rw [sq]
    exact (congrArg (fun (k : (F.obj P.right).obj B ⟶ (F.obj Q.right).obj (X × B)) => k (P.hom ⟨i,w⟩))
      ((F.map f.right).naturality (insert x B))).symm⟩

def sameGrades {C D T : Type*} [Category* C] [Category* D] [Category* T] {S : C ⥤ T} {R : D ⥤ T}
    {a : C} {b : D} {f g : S.obj a ⟶ R.obj b} (h : f = g) :
    (⟨a,b,f⟩ : Comma S R) ≅ ⟨a,b,g⟩ :=
  Comma.isoMk (Iso.refl a) (Iso.refl b) (by change S.map (𝟙 a) ≫ g = f ≫ R.map (𝟙 b); simp [h])

/-- The frame-function square is a native isomorphism, with identity carried grade components. -/
def parameter {X Y : Type u} (q : X → Y) (A B : Type u) :
    framed raw J F X ⋙ relabel raw J F (X × A) ((reparam q).app B) ≅
      framed raw J F Y ⋙ reindex raw J F ((reparam q).app A) (Y × B) :=
  NatIso.ofComponents (fun P => sameGrades (by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,i⟩,w⟩
    exact congrArg (fun (k : X × (F.obj P.right).obj B ⟶ (F.obj P.right).obj (Y × B)) => k (x,P.hom ⟨i,w⟩))
      (CanonicalSetStrength.parameter (F.obj P.right) q B).symm)) (by
    intro P Q f
    apply Comma.hom_ext _ _ <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

def frame_unit (A B : Type u) :
    framed raw J F PUnit.{u+1} ⋙ relabel raw J F _ (unitor B).hom ≅ reindex raw J F (unitor A).hom B :=
  NatIso.ofComponents (fun P => sameGrades (by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,i⟩,w⟩
    exact (congrArg (fun (k : PUnit × (F.obj P.right).obj B ⟶ (F.obj P.right).obj B) => k (x,P.hom ⟨i,w⟩))
      (unit_frame (F.obj P.right) B)))) (by intro P Q f; apply Comma.hom_ext _ _ <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

def frame_assoc (X Y A B : Type u) :
    framed raw J F Y ⋙ framed raw J F X ⋙ relabel raw J F _ (associator X Y B).hom ≅
      framed raw J F (X × Y) ⋙ reindex raw J F (associator X Y A).hom _ :=
  NatIso.ofComponents (fun P => sameGrades (by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,y,i⟩,w⟩
    exact (congrArg (fun (k : X × (Y × (F.obj P.right).obj B) ⟶ (F.obj P.right).obj ((X × Y) × B)) =>
      k (x,y,P.hom ⟨i,w⟩)) (associate_frames (F.obj P.right) X Y B))))
    (by intro P Q f; apply Comma.hom_ext _ _ <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

end ContextualComposition.ConstantGradeFraming
