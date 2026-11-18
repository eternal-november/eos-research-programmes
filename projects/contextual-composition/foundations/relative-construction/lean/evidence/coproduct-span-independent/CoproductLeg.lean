import ContextualComposition.CoproductSpan
open CategoryTheory CategoryTheory.Functor Opposite
namespace ContextualComposition.GrothendieckStep.CoproductSpan
universe i k j b w
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (A : B) (t : I)
example : Sigma.incl t ⋙ Sigma.desc p = p t := rfl
example : Sigma.incl t ⋙ Sigma.desc d = d t := rfl
example : incl p A t ⋙ wholeLeg p d A = leg p d A t := by
  exact congrArg (fun F => Sigma.incl t ⋙ F) (over p d A)
end ContextualComposition.GrothendieckStep.CoproductSpan
