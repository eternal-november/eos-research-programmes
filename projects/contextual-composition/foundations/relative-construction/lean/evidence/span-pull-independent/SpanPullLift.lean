import ContextualComposition.SpanPull
open CategoryTheory CategoryTheory.Functor Opposite
namespace ContextualComposition.GrothendieckStep.SpanPull
open NativeCleavage
universe i k j b w u v
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (C : ∀ t, Cleavage (p t)) (Y : Bᵒᵖ ⥤ Cat.{v,u})
example (A : B) (t : I) (y : K t) (a : A ⟶ (p t).obj y) :
    ((choice p C) A ⟨t,y⟩ a).lift = (Sigma.incl t).map ((C t A y a).lift) := rfl
example (A : B) (z : Total Y (Sigma.desc d)) (a : A ⟶ (Sigma.desc p).obj (grade _ _ z)) :
    ((weightedChoice p d C Y) A z a).lift = pullLift Y (Sigma.desc d) z (((choice p C) A (grade _ _ z) a).lift) := rfl
end ContextualComposition.GrothendieckStep.SpanPull
