import ContextualComposition.ContextadHorizontalModification
import ContextualComposition.ContextadChartModifications
open CategoryTheory
open ContextualComposition.GrothendieckStep
open ContextadNativeLaws ContextadHorizontalLaws
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (c : Constraints d m)
#check ContextadOuterCharts.outerTensorMod
#check ContextadStandardLaws.assoc
#check triangleModification
#check pentagonModification
/- A grade-level constraint triple is not of the interface type giving inter-cut seam cells. -/
#check_failure (c : PentagonSeams d m c)
#check_failure (c : TriangleSeams d m c)
