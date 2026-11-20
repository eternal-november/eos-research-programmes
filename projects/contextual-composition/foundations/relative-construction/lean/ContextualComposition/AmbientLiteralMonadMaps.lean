module
public import ContextualComposition.AmbientPseudomonadProjections
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientLiteralMonadMaps
open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientMonadMaps AmbientCoherentPseudomonad AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoordinates
open ContextadRoutes ContextadNativeLaws ContextadModification ContextadOuterCharts
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u v
theorem preframe {D : Type*} [Category D] {a b c : D} (e : a = b) (i : b ≅ c) : HEq (eqToIso e ≪≫ i) i := by subst b; simp
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (T : Data S) {X Y : Obj.{u,v} B} (f : X ⟶ Y)
theorem etaFrame : HEq (squareE S T.unit f) (comparison S (insert S T.unit) (unitCart T.unit) f) :=
  preframe _ _
theorem muFrame : HEq (squareM S T.mult f) (comparison S (tensor T.mult) T.mult.cart f) :=
  preframe _ _
theorem eta : HEq ((unitMap T).naturality f) (squareE S T.unit f) :=
  (AmbientMonadMapRead.etaSquare S T.unit f).trans (etaFrame T f).symm
set_option linter.defProp false in
def mu :=
  (AmbientMonadMapRead.muSquare S T.mult f).trans (muFrame T f).symm
end ContextualComposition.GrothendieckStep.AmbientLiteralMonadMaps
