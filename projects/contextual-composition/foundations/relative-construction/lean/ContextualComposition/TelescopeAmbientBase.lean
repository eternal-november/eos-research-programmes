module
public import ContextualComposition.TelescopeGradeChange
public import ContextualComposition.ContextadAmbientCartesian
public import ContextualComposition.MixedMates

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientBase

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open NativeCleavage ContextadAmbientPayload ContextadWeakAction TelescopeSquares
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

set_option backward.isDefEq.respectTransparency false
universe u v k j
variable {B : Type u} [Category.{v} B] {K : Type k} [Category.{j} K]
variable {X Y : Bᵒᵖ ⥤ Cat.{v,u}} (f : StrongTrans X.toPseudofunctor' Y.toPseudofunctor')
variable (e p : K ⥤ B)

theorem endpointOver :
    atEndpoint f e ⋙ FibreTotal.projection Y e p = FibreTotal.projection X e p :=
  congrArg (· ⋙ p) (actionGrade e (totalStrong f) (strongOver f))

noncomputable abbrev onFibre (A : B) :=
  SpanPayload.fibreFunctor (atEndpoint f e) (FibreTotal.projection Y e p) (endpointOver f e p) A

/-- Restricting an ambient map to the strict fibre gives the weighted action at its actual endpoint. -/
theorem intoSquare (A : B) :
    atEndpoint f (FibreTotal.endpoint e p A) ⋙ FibreTotal.into Y e p A =
      FibreTotal.into X e p A ⋙ onFibre f e p A := by
  apply EvalPayload.cancelInclusion
  simp only [Functor.assoc]
  rw [show onFibre f e p A ⋙ Functor.Fiber.fiberInclusion =
      Functor.Fiber.fiberInclusion ⋙ atEndpoint f e from SpanPayload.fibre_diagram _ _ _ _]
  exact (TelescopeGradeChange.totalMap_payload f (Functor.Fiber.fiberInclusion (p := p) (S := A)) e rfl).symm

theorem outSquare (A : B) :
    FibreTotal.out X e p A ⋙ atEndpoint f (FibreTotal.endpoint e p A) =
      onFibre f e p A ⋙ FibreTotal.out Y e p A :=
  congrArg (fun F => FibreTotal.out X e p A ⋙ F ⋙ FibreTotal.out Y e p A) (intoSquare f e p A)

variable (C : Cleavage p) {A D : B} (a : A ⟶ D)

/-- Each component factors the image of the chosen lift through the target lift. -/
noncomputable def cartesianFace :
    NativeCube.Face (Route.ofChoice (extendChoice X e p C) a) (Route.ofChoice (extendChoice Y e p C) a)
      (atEndpoint f e) (endpointOver f e p) :=
  ⟨Change.square _ _ _ _ (liftCart f e p C), NativeCube.changeFac _ _ _ _ (liftCart f e p C)⟩

/-- The base/strong comparison in the original weighted fibre presentation. -/
noncomputable def presented :
    TaggedMixed.Presented.pull e p C X a ⋙ atEndpoint f (FibreTotal.endpoint e p A) ≅
      atEndpoint f (FibreTotal.endpoint e p D) ⋙ TaggedMixed.Presented.pull e p C Y a :=
  NativeCube.present (FibreTotal.into X e p D) (FibreTotal.out Y e p A)
    (Reindex.functor (extendChoice X e p C) a) (Reindex.functor (extendChoice Y e p C) a)
    (onFibre f e p A) (onFibre f e p D)
    (FibreTotal.out X e p A ⋙ atEndpoint f _) (atEndpoint f _ ⋙ FibreTotal.into Y e p D)
    (cartesianFace f e p C a).sq (outSquare f e p A) (intoSquare f e p D).symm

/-- In the presentation, the comparison component is the actual factored arrow, transported by out. -/
theorem presented_component (x : Total X (FibreTotal.endpoint e p D)) :
    Aligned ((presented f e p C a).hom.app x)
      ((FibreTotal.out Y e p A).map ((cartesianFace f e p C a).sq.hom.app ((FibreTotal.into X e p D).obj x))) :=
  FinalCube.Align.stripPresent _ _ _ _ _ _ _ _ (cartesianFace f e p C a).sq
    (outSquare f e p A) (intoSquare f e p D).symm x

open CoproductSpan CoproductSpan.All
variable {Q : Endpoints.{u,v,u,v} B} (S : Q.Split)

/-- Reindexing in the single weighted telescope span commutes up to an invertible cell with every strong payload map. -/
noncomputable def whole :
    SpanPull.All.pull S X a ⋙ atEndpoint f (wholeLeg (src S) (dst S) A) ≅
      atEndpoint f (wholeLeg (src S) (dst S) D) ⋙ SpanPull.All.pull S Y a :=
  presented f (Sigma.desc (dst S)) (Sigma.desc (src S)) (SpanPull.choice (src S) (SpanPull.All.parts S)) a

end ContextualComposition.GrothendieckStep.TelescopeAmbientBase
