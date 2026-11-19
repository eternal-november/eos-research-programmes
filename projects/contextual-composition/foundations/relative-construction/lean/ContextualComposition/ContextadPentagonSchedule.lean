module
public import ContextualComposition.ContextadNestedSchedule
public import ContextualComposition.ContextadDisjointComparison
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadCellPasting ContextadHorizontalLaws
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
theorem pentStartRoute :
    (pent1 d m C).src = (pent4 d m C).src :=
  (congrArg (comp · (tensor m)) (outComp (firstTwo m) (tensor m))).trans (compAssoc _ _ _)
theorem pentEndRoute :
    (pent5 d m C).dst = (pent3 d m C).dst :=
  (congrArg (comp · (comp (lastTwo m) (tensor m))) (nested (tensor m))).trans
    (pullIn (n := 1) (lastTwo m) (tensor m) (tensor m))
noncomputable def canonicalPentagon : PentagonSeams d m C where
  start := castCell (pentStartRoute d m C)
  oneTwo := castCell (pushOut (n := 1) (tensor m) (tensor m) (tensor m))
  twoThree := castCell (pullIn (n := 1) (firstTwo m) (tensor m) (tensor m))
  fourFive := thenCell (castCell (compAssoc _ _ _).symm)
    (thenCell (ContextadCellWhisker.after (ContextadDisjointCut.disjoint (tensor m) (tensor m) m.cart) (tensor m))
      (castCell (compAssoc _ _ _)))
  finish := castCell (pentEndRoute d m C)
abbrev PentagonLaw := ∀ x, (composite (pentLong d m C (canonicalPentagon d m C))).grade.hom.app x =
  (composite (pentShort d m C (canonicalPentagon d m C))).grade.hom.app x
structure Coherent : Prop where
  triangle : TriangleLaw d m C
  pentagon : PentagonLaw d m C
theorem pentagonAt (h : PentagonLaw d m C) (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B) :
  paste Y A (pentLong d m C (canonicalPentagon d m C)) = paste Y A (pentShort d m C (canonicalPentagon d m C)) :=
  pentagon d m C (canonicalPentagon d m C) Y A h
theorem pentagonBase (h : PentagonLaw d m C) (Y : PackedCuts.Psh.{u,max u v,u,v} B) :
  modPaste Y (pentLong d m C (canonicalPentagon d m C)) (pentStartCart d m C) (ContextadModification.presIso (composite (pentLong d m C (canonicalPentagon d m C))).grade.symm (pentStartCart d m C)) =
  modPaste Y (pentShort d m C (canonicalPentagon d m C)) (pentStartCart d m C) (ContextadModification.presIso (composite (pentLong d m C (canonicalPentagon d m C))).grade.symm (pentStartCart d m C)) :=
  pentagonModification Y d m C (canonicalPentagon d m C) h
end ContextualComposition.GrothendieckStep.ContextadSchedule
