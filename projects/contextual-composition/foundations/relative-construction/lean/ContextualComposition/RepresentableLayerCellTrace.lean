module
public import ContextualComposition.RepresentableKleisliOperations
public import ContextualComposition.AmbientCellTrace
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableLayerCellTrace
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open FibreValue TelescopeSquares AmbientCellTrace AmbientCellFunctor AmbientModificationAction
open ContextadAmbientPayload AmbientBlockCells NativeBlocks WordTrace
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 750000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} (S : P.Split)
variable {Y Z : Bᵒᵖ ⥤ Cat.{u,u}} {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'}
section Generic
variable (t : StrongTrans.Modification a b) (A : B) (x : Y.obj (op A))
def includedCell := Edge.map (incl Z A) (edge ((t.app ⟨op A⟩).toNatTrans.app x))
theorem includedPin : edge ((totalCell t).app ((incl Y A).obj x)) = includedCell t A x :=
  congrArg edge (totalApp t ((incl Y A).obj x))
end Generic
variable (t : StrongTrans.Modification a b) (A : B) (x : Total Y (P.extend A))
abbrev point := (incl (PackedFree.pow S Y 1) A).obj x
noncomputable abbrev out := (blockMod S t 1).app ⟨op A⟩ |>.toNatTrans.app x
abbrev inPoint := (P.extend A).obj (grade _ _ x)
abbrev outTail := (t.app ⟨op (inPoint A x)⟩).toNatTrans.app (payload _ _ x)
noncomputable def realRead :=
  ([Edge.map (ContextadChart.one (P := P) A) (Edge.map gradeProjection (edge (out S t A x)))],
    Edge.map (NativeTrace.leaf Z (P.extend A)) (edge (out S t A x)))
def wanted :=
  ([Edge.map (ContextadChart.one (P := P) A) (Edge.map gradeProjection (idEdge x))],
    Edge.map (incl Z (inPoint A x)) (edge (outTail t A x)))
theorem indexId {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (z : C) :
    idEdge (F.obj z) = Edge.map F (idEdge z) :=
  congrArg edge (F.map_id z).symm
theorem inTrace :
    read S Y 1 (idEdge (point S A x)) =
    ([Edge.map (ContextadChart.one (P := P) A) (Edge.map gradeProjection (idEdge x))],
      idEdge ((NativeTrace.leaf Y (P.extend A)).obj x)) :=
  (congrArg (read S Y 1) (indexId (incl (PackedFree.pow S Y 1) A) x)).trans
    ((ContextadUnary.read_incl S A Y (idEdge x)).trans (congrArg (Prod.mk _) (indexId (NativeTrace.leaf Y (P.extend A)) x).symm))
noncomputable def rawOut : Edge (Total (PackedFree.pow S Z 1) (𝟭 B)) :=
  edge ((totalCell (blockMod S t 1)).app (point S A x))
theorem pinOut : rawOut S t A x = includedCell (blockMod S t 1) A x :=
  includedPin (blockMod S t 1) A x
theorem attachRead {D T : Type*} (F : D → T) (u v : D) (h : u = v) (w : T) (k : F v = w) : F u = w :=
  (congrArg F h).trans k
theorem readOut : read S Z 1 (rawOut S t A x) = realRead S t A x :=
  attachRead (read S Z 1) (rawOut S t A x) (includedCell (blockMod S t 1) A x) (pinOut S t A x)
    (realRead S t A x) (ContextadUnary.read_incl S A Z (edge (out S t A x)))
set_option linter.defProp false in
def stepIn := congrArg (fun H => (H.1,edge ((totalCell t).app H.2.src))) (inTrace S A x)
set_option linter.defProp false in
def tailStep := congrArg (Prod.mk ([Edge.map (ContextadChart.one (P := P) A) (Edge.map gradeProjection (idEdge x))]))
  (congrArg edge (totalApp t ((NativeTrace.leaf Y (P.extend A)).obj x)))
theorem exactTrace : realRead S t A x = wanted t A x :=
  (readOut S t A x).symm.trans ((trace S t 1 (point S A x)).trans ((stepIn S t A x).trans (tailStep t A x)))
end ContextualComposition.GrothendieckStep.RepresentableLayerCellTrace
