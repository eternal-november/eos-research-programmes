module
public import ContextualComposition.ContextadPayloadModification
public import ContextualComposition.ContextadCellPasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadCellWhisker
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue ContextadRoutes ContextadLawTransport
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j k l : Nat} {f g : Map S j k} (a : Cell f g)
def before (p : Map S i j) : Cell (comp p f) (comp p g) where
  grade := isoWhiskerLeft p.grade a.grade
  source x := a.source _
  endpoint := by
    apply NatTrans.ext; funext x
    change _ ≫ g.leg.app _ ≫ p.leg.app x = _
    rw [← Category.assoc]
    exact congrArg (· ≫ p.leg.app x) (NatTrans.congr_app a.endpoint (p.grade.obj x))
def after (q : Map S k l) : Cell (comp f q) (comp g q) where
  grade := isoWhiskerRight a.grade q.grade
  source x := by
    change Pure ((q.grade ⋙ (power S l).source).map (a.grade.hom.app x))
    rw [q.over]; exact a.source x
  endpoint := by
    apply NatTrans.ext; funext x
    change (q.grade ⋙ (power S l).dest).map (a.grade.hom.app x) ≫ q.leg.app _ ≫ g.leg.app x = _
    exact (Category.assoc ..).symm.trans ((congrArg (· ≫ g.leg.app x) (q.leg.naturality (a.grade.hom.app x))).trans ((Category.assoc ..).trans (congrArg (q.leg.app _ ≫ ·) (NatTrans.congr_app a.endpoint x))))
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem readGrade (x) : gradeMap ((rawCell Y a).hom.app x) = a.grade.hom.app (grade Y _ x) := WeightedCells.weightGrade Y _ _ a.grade a.endpoint x
theorem readPure (x) : Pure (payloadMap ((rawCell Y a).hom.app x)) := WeightedCells.weightPayloadPure Y _ _ a.grade a.endpoint x
theorem rawCompose {i j k} (p : Map S i j) (q : Map S j k) :
    raw Y (comp p q) = raw Y p ⋙ raw Y q := restrict_paste .. 
theorem castGrade {i j k} (p : Map S i j) (q : Map S j k) (x : Total Y (power S i).dest) :
    gradeMap (eqToHom (Functor.congr_obj (rawCompose Y p q) x)) = 𝟙 _ := by
  change gradeProjection.map (eqToHom _) = _
  rw [eqToHom_map]; rfl
theorem beforeSquare (p : Map S i j) :
    (rawCell Y (before a p)).hom ≫ eqToHom (rawCompose Y p g) =
    eqToHom (rawCompose Y p f) ≫ whiskerLeft (raw Y p) (rawCell Y a).hom := by
  ext x : 2
  simp only [NatTrans.comp_app,whiskerLeft_app,eqToHom_app]
  apply WeightedCells.pureArrowEq Y _
  · rw [grade_comp,grade_comp,castGrade,castGrade,Category.id_comp,Category.comp_id]
    exact (readGrade (before a p) Y x).trans (readGrade a Y ((raw Y p).obj x)).symm
  · exact WeightedCells.totalPureComp Y _ (readPure (before a p) Y x) (ContextadPayloadModification.pureCast _ _)
  · exact WeightedCells.totalPureComp Y _ (ContextadPayloadModification.pureCast _ _) (readPure a Y ((raw Y p).obj x))
theorem afterSquare (q : Map S k l) :
    (rawCell Y (after a q)).hom ≫ eqToHom (rawCompose Y g q) =
    eqToHom (rawCompose Y f q) ≫ whiskerRight (rawCell Y a).hom (raw Y q) := by
  ext x : 2
  simp only [NatTrans.comp_app,whiskerRight_app,eqToHom_app]
  apply WeightedCells.pureArrowEq Y _
  · rw [grade_comp,grade_comp,castGrade,castGrade,Category.id_comp,Category.comp_id]
    exact (readGrade (after a q) Y x).trans (congrArg q.grade.map (readGrade a Y x)).symm
  · exact WeightedCells.totalPureComp Y _ (readPure (after a q) Y x) (ContextadPayloadModification.pureCast _ _)
  · apply WeightedCells.totalPureComp Y _ (ContextadPayloadModification.pureCast _ _)
    rw [show payloadMap ((raw Y q).map ((rawCell Y a).hom.app x)) = _ from restrict_payload Y _ _ q.grade q.leg _]
    exact pureComp (pureMap _ (readPure a Y x)) ⟨_,rfl⟩
end ContextualComposition.GrothendieckStep.ContextadCellWhisker
