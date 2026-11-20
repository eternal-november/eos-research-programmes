module
public import ContextualComposition.AmbientHorizontalDiagrams
public import ContextualComposition.AmbientHorizontalRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientExchangeDemand
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadHorizontalLaws AmbientHorizontalRead AmbientHorizontalDiagrams ContextadDisjointCut
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) (m : ContextadTotal.Native S)
noncomputable def interchange :
    M S (obj S 2 X) m ≫ K S (M S X m) ≅ K S (K S (M S X m)) ≫ M S (obj S 1 X) m :=
  (squareM S m (M S X m)).symm
abbrev Law : Prop := Reads (S := S) (X := X) (j := 4) (k := 2) (r := lhs (tensor m) (tensor m)) (s := rhs (tensor m) (tensor m)) (interchange X m).hom (disjoint (tensor m) (tensor m) m.cart)
def whiskered (h : Law X m) :=
  post (S := S) (X := X) (j := 4) (k := 2) (l := 1) (a := (interchange X m).hom) (c := disjoint (tensor m) (tensor m) m.cart) h (M S X m) (tensor m) (opEncode S (tensor m) m.cart X)
end ContextualComposition.GrothendieckStep.AmbientExchangeDemand
