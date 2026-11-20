module
public import ContextualComposition.AmbientBoundaryReduction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientMultiplicationSpoke
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory
open AmbientBicategory AmbientCoordinates AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientHorizontalNaturality
open AmbientBoundaryReduction AmbientSquareBridge ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadModification
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1550000
attribute [local irreducible] BlockEvaluation.global AmbientModificationAction.totalCell ContextadAmbientPayload.totalStrong
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} (f : X ⟶ Y) (m : ContextadTotal.Native S)
variable {i : Nat}
variable {z : obj S i X ⟶ obj S i Y} (hz : z = AmbientBicategory.map S i f)
variable {a : obj S i X ⟶ obj S 2 X} {b : obj S i Y ⟶ obj S 2 Y}
variable (r : Map S i 2) (p : gradeCart (S := S) (i := i) (j := 1) (comp (i := i) (j := 2) (k := 1) r (tensor m)))
variable (e : global (S := S) (i := i) (j := 2) (underlying X) r = tot (V := obj S i X) (W := obj S 2 X) a) (w : global (S := S) (i := i) (j := 2) (underlying Y) r = tot (V := obj S i Y) (W := obj S 2 Y) b)
variable (s : z ≫ b ≅ a ≫ K S (X := obj S 1 X) (Y := obj S 1 Y) (K S f))
set_option linter.defProp false in
def installed (Z : Obj.{u,v} B) (u : obj S i Z ⟶ obj S 2 Z) (j : global (S := S) (i := i) (j := 2) (underlying Z) r = tot (V := obj S i Z) (W := obj S 2 Z) u) :=
  route S Z (i := i) (j := 2) (k := 1) r (tensor m) p m.cart u j
set_option linter.defProp false in
def glued (h : RRead (i := i) (j := 2) S f s r) :=
  serialRaw (i := i) (j := 2) (k := 1) S f s (squareM S m f) r (tensor m) h (muRead S f m)
    (AmbientDeepIndices.encodedOfTotal S X (i := i) (j := 2) a r e.symm) (opEncode S (tensor m) m.cart Y)
set_option linter.defProp false in
def seam (h : RRead (i := i) (j := 2) S f s r) :=
  toBend (i := i) (j := 1) S f hz (comp r (tensor m)) p (installed m r p X a e) (installed m r p Y b w)
    (serial s (squareM S m f)) (glued f m r e s h)
end ContextualComposition.GrothendieckStep.AmbientMultiplicationSpoke
