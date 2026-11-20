module
public import ContextualComposition.ContextadAmbientIsoMod
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientVerticalDescent
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage FibreValue TelescopeSquares ContextadLawTransport ContextadModification
set_option backward.isDefEq.respectTransparency false
universe u v
section
variable {K L B : Type*} [Category* K] [Category* L] [Category* B]
variable {p : K ⥤ B} {q : L ⥤ B} {F G : K ⥤ L} (h : F ⋙ q = p) (k : G ⋙ q = p)
variable (i : F ⟶ G) (v : ∀ x, Pure (q.map (i.app x)))
def fibre (A : B) : SpanPayload.fibreFunctor F q h A ⟶ SpanPayload.fibreFunctor G q k A := by
  let t := eqToHom (SpanPayload.fibre_diagram F q h A) ≫ whiskerLeft Fiber.fiberInclusion i ≫ eqToHom (SpanPayload.fibre_diagram G q k A).symm
  refine { app := fun x => ⟨t.app x,pureLift _ ?_⟩, naturality := fun _ _ f => Subtype.ext (t.naturality f) }
  simp only [t,NatTrans.comp_app,eqToHom_app,whiskerLeft_app,Functor.map_comp,eqToHom_map]
  exact pureComp ⟨_,rfl⟩ (pureComp (v _) ⟨_,rfl⟩)
theorem underlying (A : B) (x : p.Fiber A) :
    Aligned (((fibre h k i v A).app x).val) (i.app x.val) := by
  refine ⟨Functor.congr_obj (SpanPayload.fibre_diagram F q h A) x,Functor.congr_obj (SpanPayload.fibre_diagram G q k A) x,?_⟩
  simp [fibre,eqToHom_app]; rfl
variable (pf : Pres F p q) (pg : Pres G p q)
theorem square {A D : B} {a : A ⟶ D} (R : Route p a) (Q : Route q a) (x : p.Fiber D) :
    (Change.square F h R Q pf).hom.app x ≫ Q.act.map ((fibre h k i v D).app x) =
      (fibre h k i v A).app (R.act.obj x) ≫ (Change.square G k R Q pg).hom.app x := by
  apply DecoderCube.CommonLift.compare Q _ _ _ _ _ _ rfl rfl
  exact (((NativeCube.changeFac F h R Q pf x).comp (underlying h k i v D x)).trans
    ((NativeCube.ofEq (i.naturality (R.lift x))).trans
    ((underlying h k i v A (R.act.obj x)).comp (NativeCube.changeFac G k R Q pg x)).symm)).eq
end
variable {B : Type*} [Category* B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u})
variable {F G : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)} (h : F ⋙ proj Z = proj Y) (k : G ⋙ proj Z = proj Y)
variable (i : F ⟶ G) (v : ∀ x, Pure ((proj Z).map (i.app x)))
noncomputable abbrev localCell (A : B) := whiskerLeft (embed Y A) (whiskerRight (fibre h k i v A) (value Z A))
variable (pf : Pres F (proj Y) (proj Z)) (pg : Pres G (proj Y) (proj Z))
theorem localSquare {A D : B} (a : A ⟶ D) (x : Y.obj (op D)) :
    (ContextadTotal.valueSquare Y Z F h pf a).hom.app x ≫
      (Z.map a.op).toFunctor.map ((localCell Y Z h k i v D).app x) =
    (localCell Y Z h k i v A).app ((Y.map a.op).toFunctor.obj x) ≫
      (ContextadTotal.valueSquare Y Z G k pg a).hom.app x := by
  let R := Route.ofChoice (choice Y) a
  let Q := Route.ofChoice (choice Z) a
  let E := (embed Y D).obj x
  exact grid (value Z A) _ _ _ _ _ _ _ _ _ _ ((fibre h k i v A).naturality ((FibreValue.square Y a).hom.app x))
    (square h k i v pf pg R Q E) ((valueSquare Z a).hom.naturality ((fibre h k i v D).app E))
noncomputable def descend :
    Pseudofunctor.StrongTrans.Modification (decodedStrong Y Z F h pf) (decodedStrong Y Z G k pg) where
  app A := (localCell Y Z h k i v A.as.unop).toCatHom₂
  naturality {A D} a := by
    apply Cat.Hom₂.ext
    ext x : 2
    exact (localSquare Y Z h k i v pf pg a.as.unop x).symm
end ContextualComposition.GrothendieckStep.AmbientVerticalDescent
