module
public import ContextualComposition.RepresentableYonedaCounit
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableYoneda
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open ContextadCoherence FibreValue
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe b u
variable {B : Type b} [Category.{u} B] {Q : Bᵒᵖ ⥤ Cat.{u,u}} {A : B}
local instance yonedaHomCat (F G : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat.{u,u}) : Category (StrongTrans F G) := StrongTrans.homCategory
theorem cellExt {F G : Hom Q A} {t k : F ⟶ G} (h : ∀ {D : B} (f : D ⟶ A), atCell Q A t f = atCell Q A k f) : t = k := by
  apply StrongTrans.Hom.ext
  apply StrongTrans.Modification.ext
  funext D
  apply Cat.Hom₂.ext
  ext z : 2
  exact h z.as
theorem extendingNaturality {x y : Q.obj (op A)} (k : x ⟶ y) {D E : B} (a : E ⟶ D) (f : D ⟶ A) :
    (restrict (Q := Q) (a ≫ f)).map k ≫ (sq (extend Q A y) a f).hom =
      (sq (extend Q A x) a f).hom ≫ (restrict (Q := Q) a).map ((restrict (Q := Q) f).map k) := by
  rw [sqExtend, sqExtend]
  simpa only [Functor.comp_map,eqToHom_app] using (eqToHom (strictComp Q a f)).naturality k
def extendCell {x y : Q.obj (op A)} (k : x ⟶ y) : extend Q A x ⟶ extend Q A y := ⟨{
  app D := (Discrete.natTrans fun f => (restrict (Q := Q) f.as).map k).toCatHom₂
  naturality {D E} a := by
    apply Cat.Hom₂.ext
    ext f : 2
    exact extendingNaturality k a.as.unop f.as
}⟩
variable (Q A)
def extending : Q.obj (op A) ⥤ Hom Q A where
  obj := extend Q A
  map := extendCell
  map_id x := by apply cellExt; intro D f; exact (restrict (Q := Q) f).map_id x
  map_comp k h := by apply cellExt; intro D f; exact (restrict (Q := Q) f).map_comp k h
theorem rightInverse : extending Q A ⋙ evaluate Q A = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (Q.map_id (op A))
variable {Q A}
def reconstruction (F : Hom Q A) : F ≅ extend Q A (seed F) :=
  StrongTrans.isoMk (fun D => Cat.Hom.isoMk (Discrete.natIso fun f => counitAt F f.as)) (fun {D E} a => by
    apply Cat.Hom₂.ext
    ext f : 2
    exact counitSquare F a.as.unop f.as)
variable (Q A)
def leftInverse : 𝟭 (Hom Q A) ≅ evaluate Q A ⋙ extending Q A :=
  NatIso.ofComponents reconstruction (fun t => by
    apply cellExt; intro D f
    exact counitNatural t f)
def equivalence : Hom Q A ≌ Q.obj (op A) :=
  CategoryTheory.Equivalence.mk (evaluate Q A) (extending Q A) (leftInverse Q A) (eqToIso (rightInverse Q A))
end ContextualComposition.GrothendieckStep.RepresentableYoneda
