import ContextualComposition.PullLaws
open CategoryTheory CategoryTheory.Functor Opposite
namespace ContextualComposition.GrothendieckStep.PullLaws
open NativeCleavage SpanPull CoproductSpan
universe i k j b w u v
variable {I : Type i} {B : Type b} [Category.{w} B] {K : I → Type k} [∀ t, Category.{j} (K t)]
variable (p d : ∀ t, K t ⥤ B) (C : ∀ t, Cleavage (p t)) (Y : Bᵒᵖ ⥤ Cat.{v,u})
example (A : B) :
    (forward p d C Y (𝟙 A)).inv ≫ whiskerLeft (compare p d A Y) (wholeUnit p d C Y A).hom =
    whiskerRight (taggedUnit p d C Y A) (compare p d A Y) :=
  NatTrans.ext (funext (forwardUnit p d C Y A))
example {A D E : B} (a : A ⟶ D) (b : D ⟶ E) :
    (forward p d C Y (a ≫ b)).inv ≫ whiskerLeft (compare p d E Y) (wholeComp p d C Y a b).hom =
      whiskerRight (taggedComp p d C Y a b) (compare p d A Y) ≫
        whiskerLeft (ZeroPower.Sum.map (componentPull p d C Y b)) (forward p d C Y a).inv ≫
        whiskerRight (forward p d C Y b).inv (wholePull p d C Y a) :=
  NatTrans.ext (funext (forwardComp p d C Y a b))
end ContextualComposition.GrothendieckStep.PullLaws
