module
public import ContextualComposition.RepresentableKleisliData
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableRestrictionBoundary
open CategoryTheory Opposite CategoryTheory.Bicategory
open AmbientBicategory RepresentableKleisli
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} (S : P.Split)
def empty : Obj.{u,u} B := (Functor.const _).obj (Cat.of (Discrete PEmpty.{u+1}))
theorem emptyK (A : B) : ¬ Nonempty (yObj A ⟶ obj.{u,u} S 1 (empty (B := B))) := by
  rintro ⟨f⟩
  let q := RepresentableYoneda.atPoint (underlying.{u,u} (obj.{u,u} S 1 (empty (B := B)))) A f.hom (𝟙 A)
  let z : Discrete PEmpty.{u+1} := payload (underlying.{u,u} (empty (B := B))) (P.extend A) q
  exact z.as.elim
end ContextualComposition.GrothendieckStep.RepresentableRestrictionBoundary
