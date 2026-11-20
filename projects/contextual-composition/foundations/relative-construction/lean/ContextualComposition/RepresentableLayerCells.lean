module
public import ContextualComposition.RepresentableLayerCellTrace
public import ContextualComposition.RepresentableLayerNaturality
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableLayerCells
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite CategoryTheory.Bicategory
open FibreValue TelescopeSquares AmbientCellTrace AmbientCellFunctor AmbientModificationAction
open ContextadAmbientPayload AmbientBlockCells NativeBlocks WordTrace ContextadWeakAction
open RepresentableLayerCellTrace
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
universe u
theorem edgeInjective {C D : Type*} [Category* C] [Category* D] (i : C ⥤ D) [i.Faithful] (j : Function.Injective i.obj) :
    Function.Injective (Edge.map i) := by
  intro x y h
  have e := j (congrArg Edge.src h)
  have w := j (congrArg Edge.dst h)
  obtain ⟨p,q,f⟩ := x
  obtain ⟨p',q',g⟩ := y
  change p = p' at e; change q = q' at w
  subst p'; subst q'
  exact congrArg edge (i.map_injective (eq_of_heq (Edge.hom_heq h)))
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} (S : P.Split)
variable {Z : Bᵒᵖ ⥤ Cat.{u,u}} (A : B)
def viewEdge (z : Edge (Total Z (P.extend A))) :=
  ([Edge.map (ContextadChart.one (P := P) A) (Edge.map gradeProjection z)], Edge.map (NativeTrace.leaf Z (P.extend A)) z)
include S in
theorem viewInjective : Function.Injective (viewEdge (P := P) (Z := Z) A) := by
  intro y z h
  let L := (PackedFree.pow S Z 1)
  let F := incl L A
  let : F.Faithful := (inferInstance : (embed L A ⋙ Fiber.fiberInclusion).Faithful)
  have inj : Function.Injective F.obj := by
    intro x y e
    have h := congrArg (BlockEvaluation.totalPoints L (𝟭 B)) e
    change (Sigma.mk A x : Σ a : B, L.obj (op a)) = Sigma.mk A y at h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply edgeInjective F inj
  apply read_injective S Z 1
  exact (ContextadUnary.read_incl S A Z y).trans (h.trans (ContextadUnary.read_incl S A Z z).symm)
variable {Y : Bᵒᵖ ⥤ Cat.{u,u}} {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'}
variable (t : StrongTrans.Modification a b) (x : Total Y (P.extend A))
theorem localRead : viewEdge A (edge ((endpointCell (P.extend A) t).app x)) = wanted t A x := by
  apply Prod.ext
  · apply congrArg (fun w => [Edge.map (ContextadChart.one (P := P) A) w])
    exact (edgePure (endpointOver (P.extend A) t x)).trans
      ((congrArg idEdge (Functor.congr_obj (actionGrade (P.extend A) (totalStrong a) (strongOver a)) x)).trans
         (indexId gradeProjection x))
  · change edge ((NativeTrace.leaf Z (P.extend A)).map ((endpointCell (P.extend A) t).app x)) = _
    exact (congrArg edge (endpointLeaf (P.extend A) t x)).trans
      ((reframe _ _ _ _).trans (congrArg edge (totalApp t ((NativeTrace.leaf Y (P.extend A)).obj x))))
theorem localCell : edge (out S t A x) = edge ((endpointCell (P.extend A) t).app x) :=
  viewInjective S A ((exactTrace S t A x).trans ((localRead A t x).symm))
end ContextualComposition.GrothendieckStep.RepresentableLayerCells
