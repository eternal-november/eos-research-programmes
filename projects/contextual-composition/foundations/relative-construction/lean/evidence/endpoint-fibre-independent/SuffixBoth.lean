import ContextualComposition.EndpointValues
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep
open SpanApex MovingCoordinates MovingCell ProjectedCharts FibreEndpoints
namespace IndependentSuffix
section Generic
variable {B K J L : Type*} [Category* B] [Category* K] [Category* J] [Category* L]
variable (e : K ⥤ B) (p : J ⥤ B) (q : L ⥤ B) {F G : J ⥤ L} (h : F ⋙ q = p) (k : G ⋙ q = p)
variable (i : F ≅ G) (v : SuffixCell.vertical p q h k i.hom)
theorem both :
  whiskerRight (SuffixCell.alongIsoCell e p q h k i v).hom (Strict.snd e q) =
      whiskerLeft (Strict.snd e p) i.hom ∧
  whiskerRight (SuffixCell.alongIsoCell e p q h k i v).inv (Strict.snd e q) =
      whiskerLeft (Strict.snd e p) i.inv := ⟨rfl,rfl⟩
end Generic
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) (Y : WordTrace.Pr (B := B)) {K : Type*} [Category* K] (e : K ⥤ B)
example := both e (base S Y) (proj S Y) (leftOver S Y) (rightOver S Y) (cell S Y) (totalVertical S Y)
end IndependentSuffix
