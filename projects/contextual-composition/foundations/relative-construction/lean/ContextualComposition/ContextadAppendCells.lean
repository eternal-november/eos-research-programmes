module
public import ContextualComposition.ContextadCellWhisker
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAppendCells
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue ContextadRoutes ContextadLawTransport
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
structure ApexCell {U V : Span (B := B)} (r s : Operation U V) where
  grade : r.grade ≅ s.grade
  src : ∀ x, Pure (V.source.map (grade.hom.app x))
  tip : whiskerRight grade.hom V.dest ≫ s.leg = r.leg
variable {U V : Span (B := B)} {r s : Operation U V} (c : ApexCell r s)
abbrev appendIso := WeightedCells.weightIso P.grades U.dest V.dest c.grade c.tip
theorem tipSquare (x : Total P.grades U.dest) :
    (second P V.dest).map ((appendIso (P := P) c).hom.app x) ≫ (suffixRaw (P := P) (U := U) (V := V) s.grade s.leg).app x =
    (suffixRaw (P := P) (U := U) (V := V) r.grade r.leg).app x := by
  apply WeightedCells.pureArrowEq P.grades (𝟭 B)
  · rw [grade_comp]
    change V.dest.map (gradeMap ((appendIso (P := P) c).hom.app x)) ≫ s.leg.app _ = r.leg.app _
    rw [show gradeMap ((appendIso (P := P) c).hom.app x) = _ from WeightedCells.weightGrade P.grades U.dest V.dest c.grade c.tip x]
    exact NatTrans.congr_app c.tip _
  · exact WeightedCells.totalPureComp _ _ (WeightedCells.weightPayloadPure P.grades U.dest V.dest c.grade c.tip x) (pureId _)
  · exact pureId _
def appendCell : ApexCell (appendMap (S := S) r) (appendMap (S := S) s) where
  grade := appendIso c
  src x := by
    change Pure (V.source.map (gradeMap ((appendIso (P := P) c).hom.app x)))
    rw [show gradeMap ((appendIso (P := P) c).hom.app x) = _ from WeightedCells.weightGrade P.grades U.dest V.dest c.grade c.tip x]
    exact c.src _
  tip := by
    apply NatTrans.ext; funext x
    exact ((right P S).map_comp _ _).symm.trans (congrArg (right P S).map (tipSquare c x))
variable {i j : Nat} {p q : Map S i j} (a : Cell p q)
def asApex : ApexCell p q := ⟨a.grade,a.source,a.endpoint⟩
def asCell (b : ApexCell p q) : Cell p q := ⟨b.grade,b.src,b.tip⟩
noncomputable def suffixCell : Cell (suffix p) (suffix q) := by
  cases i <;> cases j <;> exact asCell (appendCell (asApex a))
end ContextualComposition.GrothendieckStep.ContextadAppendCells
