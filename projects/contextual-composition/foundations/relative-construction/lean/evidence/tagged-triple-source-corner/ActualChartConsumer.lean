import ContextualComposition.TaggedSquareRecognition
open CategoryTheory ContextualComposition.GrothendieckStep TaggedTripleFaces TaggedSquareRecognition
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
example := onCharts S Y (first S Y).hom (last S Y).hom (sourceCorner S Y).hom
