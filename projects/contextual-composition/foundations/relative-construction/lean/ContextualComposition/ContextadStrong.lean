module
public import ContextualComposition.ContextadCoherence
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadStrong
open CategoryTheory CategoryTheory.Functor Opposite Bicategory
open ContextadCoherence FibreValue
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
section General
variable {B : Type*} [Category* B] {G H : Bᵒᵖ ⥤ Cat.{v,u}}
variable (F : ∀ A : B, G.obj (op A) ⥤ H.obj (op A))
variable (s : ∀ {A D : B} (a : D ⟶ A), (G.map a.op).toFunctor ⋙ F D ≅ F A ⋙ (H.map a.op).toFunctor)
variable (unitLaw : ∀ A : B, Paste.UnitLaw (s (𝟙 A)) (eqToHom (strictUnit G A)) (eqToHom (strictUnit H A)))
variable (compLaw : ∀ {A D E : B} (a : A ⟶ D) (b : D ⟶ E),
  Paste.CompLaw (s (a ≫ b)) (s a) (s b) (eqToHom (strictComp G a b)) (eqToHom (strictComp H a b)))
def assemble : Pseudofunctor.StrongTrans G.toPseudofunctor' H.toPseudofunctor' where
  app A := (F A.as.unop).toCatHom
  naturality f := Cat.Hom.isoMk (s f.as.unop)
  naturality_naturality {a b} {f g} η := by
    have : f = g := LocallyDiscrete.eq_of_hom η
    subst g
    have e : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id A := by
    obtain ⟨A⟩ := A
    apply Cat.Hom₂.ext
    ext x : 2
    simpa [Functor.toPseudofunctor'_mapId,Cat.Hom₂.eqToHom_toNatTrans,strictUnit,eqToHom_map] using unitLaw A.unop x
  naturality_comp {a b c} f g := by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    obtain ⟨c⟩ := c
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    apply Cat.Hom₂.ext
    ext x : 2
    have h := compLaw g.unop f.unop x
    simp only [eqToHom_app,eqToHom_map] at h
    simp [Functor.toPseudofunctor'_mapComp,Cat.Hom₂.eqToHom_toNatTrans]
    exact h
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
noncomputable def multiplication :
    Pseudofunctor.StrongTrans (source (S := S) Y).toPseudofunctor' (target (S := S) Y).toPseudofunctor' :=
  assemble (G := source (S := S) Y) (H := target (S := S) Y) (actual m Y) (fun a => exterior m Y a) (unit m Y) (fun a b => comp m Y a b)
end ContextualComposition.GrothendieckStep.ContextadStrong
