module
public import ContextualComposition.ContextadMixedSchedule
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadCellPasting ContextadHorizontalLaws
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
theorem pushOut {n i j k l : Nat} (f : Map S i j) (g : Map S (n+j) k) (h : Map S (k+1) l) :
    comp (suffix (comp (inside n f) g)) h = comp (inside n (suffix f)) (comp (suffix g) h) :=
  (congrArg (comp · h) (outComp (inside n f) g)).trans ((compAssoc _ _ _).trans (congrArg (comp · (comp (suffix g) h)) (mixed n f)))
theorem pullIn {n i j k l : Nat} (f : Map S i j) (g : Map S j k) (h : Map S (n+k) l) :
    comp (inside n f) (comp (inside n g) h) = comp (inside n (comp f g)) h :=
  (compAssoc _ _ _).symm.trans (congrArg (comp · h) (inComp n f g))
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
noncomputable def canonicalTriangle : TriangleSeams d m C where
  start := castCell (pushOut (n := 1) (insert S d) (tensor m) (tensor m))
  middle := castCell (pullIn (n := 1) (leftUnit d) (tensor m) (tensor m))
  finish := castCell (congrArg (comp · (tensor m)) ((inId (S := S) 1 1).trans (outId 1).symm))
abbrev TriangleLaw := ∀ x, (composite (triLong d m C (canonicalTriangle d m C))).grade.hom.app x =
  (composite (triShort d m C)).grade.hom.app x
theorem triangleAt (h : TriangleLaw d m C) (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B) :
  paste Y A (triLong d m C (canonicalTriangle d m C)) = paste Y A (triShort d m C) :=
  triangle d m C (canonicalTriangle d m C) Y A h
theorem triangleBase (h : TriangleLaw d m C) (Y : PackedCuts.Psh.{u,max u v,u,v} B) :
  modPaste Y (triLong d m C (canonicalTriangle d m C)) (triStartCart d m C) (ContextadModification.presIso (composite (triShort d m C)).grade.symm (triStartCart d m C)) =
  modPaste Y (triShort d m C) (triStartCart d m C) (ContextadModification.presIso (composite (triShort d m C)).grade.symm (triStartCart d m C)) :=
  triangleModification Y d m C (canonicalTriangle d m C) h
end ContextualComposition.GrothendieckStep.ContextadSchedule
