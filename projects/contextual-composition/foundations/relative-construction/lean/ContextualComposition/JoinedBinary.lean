module
public import ContextualComposition.TaggedSquareRecognition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.JoinedBinary
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked MovingCoordinates MovingCell ProjectedCharts FibreEndpoints ChartRealization TaggedTripleFaces
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem glueSwap (K : C ⥤ D) (R : D ⥤ C) (k : R ⋙ K ≅ 𝟭 D) (F : D ⥤ E) (U V : C ⥤ E)
    (i : K ⋙ F = U) (j : K ⋙ F = V) (h : R ⋙ U = R ⋙ V) :
    eqToHom h ≫ (glue K R k F V j).hom = (glue K R k F U i).hom := by
  subst U; subst V; simp
theorem cancelFrames {F G T : C ⥤ D} (e : F = G) {X Z : C → D} (l : ∀ x, X x ≅ F.obj x) (r : ∀ x, Z x ≅ G.obj x)
    (u : F ≅ T) (v : G ≅ T) (h : eqToHom e ≫ v.hom = u.hom) :
    (paste (eqToIso e) l r).hom ≫ (gauge G r ≪≫ v).hom = (gauge F l ≪≫ u).hom := by
  change ((gauge F l).hom ≫ eqToHom e ≫ (gauge G r).inv) ≫ (gauge G r).hom ≫ v.hom = _
  simp only [Category.assoc,Iso.inv_hom_id_assoc]; rw [h]; rfl
end General
universe u v
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
theorem cutJoined (i : Nat × Nat) : Lift.total (Lift.comp (cut S i) (NativePacked.tagged S i)) Y ⋙ binaryStages S Y = refR S Y i :=
  (CutReadout.readout S Y i).trans (congrArg (· ⋙ push S Y i) (BlockCompositor.total S Y i.1 i.2))
theorem readJoined : (MovingCoordinates.chart S Y).functor ⋙ binaryStages S Y = Sigma.desc (refR S Y) := by
  apply PackedFree.sigma_ext; intro i
  exact (congrArg (· ⋙ binaryStages S Y) (chartAt S Y i)).trans (cutJoined S Y i)
noncomputable def frame := glue (MovingCoordinates.chart S Y).functor (read S Y) (recover S Y)
  (binaryStages S Y) (Sigma.desc (refR S Y)) (readJoined S Y)
noncomputable def joined := gauge (R S Y) (MovingCell.right S Y) ≪≫ frame S Y
theorem forwardTransport {C D : Type*} [Category* C] [Category* D] (q : C ⥤ D) {x y : C} (i : x ≅ y)
    (h : IsTransport i.inv) : IsTransport (q.map i.hom) := by
  obtain ⟨e,he⟩ := h
  have k : i.hom = eqToHom e.symm := by
    apply (cancel_mono i.inv).mp
    rw [i.hom_inv_id,he]; simp
  rw [k]; exact castMap q _
theorem projectedJoined (x : X S Y) : IsTransport ((proj S Y).map ((joined S Y).hom.app x)) :=
  composeCast _ (gauge (R S Y) (MovingCell.right S Y)) _ (fun y => forwardTransport (proj S Y) (MovingCell.right S Y y) (rightCast S Y y))
    (glueCast (MovingCoordinates.chart S Y).functor (read S Y) (recover S Y) (binaryStages S Y) (Sigma.desc (refR S Y))
      (readJoined S Y) (proj S Y) (base S Y) (binaryOver S Y) (adjustCast S Y)) x
theorem vertical : SuffixCell.vertical (base S Y) (proj S Y) (rightOver S Y) (binaryOver S Y) (joined S Y).hom :=
  fun x => (projectedJoined S Y x).choose_spec
theorem compatible : (cell S Y).hom ≫ (joined S Y).hom = (CutReadout.bridge S Y).hom :=
  cancelFrames (refEq S Y) (MovingCell.left S Y) (MovingCell.right S Y) _ _ (glueSwap
    (MovingCoordinates.chart S Y).functor (read S Y) (recover S Y) (binaryStages S Y) (Sigma.desc (refL S Y))
    (Sigma.desc (refR S Y)) (allRead S Y (CutReadout.readout S Y)) (readJoined S Y) (refEq S Y))
end ContextualComposition.GrothendieckStep.JoinedBinary
