module
public import ContextualComposition.ContextadChosenCone
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterRigidity
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares NativeCleavage BoundaryPaste
open ContextadOuterCharts ContextadRoutes ContextadLawTransport ContextadChosenCone WordTrace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
universe u v
section General
variable {B K X : Type*} [Category* B] [Category* K] [Category* X] {Y : Bᵒᵖ ⥤ Cat.{v,u}} {e : K ⥤ B}
theorem payloadAligned {x y x' y' : Total Y e} {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g) (p : FibreValue.Pure (payloadMap g)) :
    FibreValue.Pure (payloadMap f) := by obtain ⟨rfl,rfl,h⟩ := h; simp at h; exact h ▸ p
theorem pureCastFactor {D C T : Type*} [Category* D] [Category* C] [Category* T] (π : D ⥤ T)
    {F G H : C ⥤ D} (l : F ⟶ H) (r : G ⟶ H) (base : F ⋙ π = G ⋙ π) (over hr)
    (v : ∀ x, Aligned (l.app x) (r.app x)) (x : C) : FibreValue.Pure (factor π l r base over hr x) := by
  refine ⟨(v x).src, cancel π _ (hr x) _ _ ?_ ?_⟩
  · rw [factorOver,eqToHom_map]
  · rw [factorFac]; simpa using (v x).comm
theorem pureMate {B : Type u} [Category.{v} B] (Y : Bᵒᵖ ⥤ Cat.{v,u}) (e : K ⥤ B) (F G : X ⥤ Total Y e)
    (gr : F ⋙ gradeProjection = G ⋙ gradeProjection)
    (i : F ⋙ second (projectionData Y) e ≅ G ⋙ second (projectionData Y) e)
    (v : ∀ x, FibreValue.Pure ((pr Y).map (i.hom.app x))) (p : ∀ x, FibreValue.Pure (i.hom.app x)) (x : X) :
    FibreValue.Pure ((mateIso Y e F G gr i v).hom.app x) := by
  let J := (whiskeringRight X _ _).obj (intoPullback (projectionData Y) e)
  have z : J.map ((mateIso Y e F G gr i v).hom) = mate Y e F G gr i.hom v := J.map_preimage _
  have h := congrArg (fun f => CategoryTheory.Limits.CategoricalPullback.Hom.snd f) (NatTrans.congr_app z x)
  apply ContextadUnitTotal.pureTotal Y e _ (mateGrade Y e F G gr i v x)
  change FibreValue.Pure (payloadMap ((second (projectionData Y) e).map ((mateIso Y e F G gr i v).hom.app x)))
  change (second (projectionData Y) e).map _ = i.hom.app x at h
  rw [h]
  obtain ⟨t,k⟩ := p x
  rw [k]; exact ContextadPayloadModification.pureCast _ _ 
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) {U V : Span (B := B)} (r : Operation U V)
set_option maxHeartbeats 2200000 in
theorem decodedChosen {a b : Total Y (right P S)} (f : a ⟶ b)
    (p : FibreValue.Pure (payloadMap (gradeMap f))) (q : FibreValue.Pure (payloadMap f)) :
    FibreValue.Pure (payloadMap ((BlockEvaluation.global S Y 1).map f)) := by
  let w : Edge (Total Y (power S 1).dest) := ⟨a,b,f⟩
  let z := Edge.map (BlockEvaluation.global S Y 1) w
  have t := NativeTrace.read_global S Y 1 w
  change ([(one S Y z).1],(one S Y z).2) = ([Edge.map gradeProjection w], Edge.map (NativeTrace.leaf Y _) w) at t
  have pa : FibreValue.Pure (payloadMap (one S Y z).1.hom) := by
    rw [(List.cons.inj (congrArg Prod.fst t)).1]; exact p
  have pb : FibreValue.Pure (payloadMap (one S Y z).2.hom) := by
    rw [congrArg Prod.snd t]; exact q
  exact ContextadUnitTotal.pureOne.{u,v} (S := S) Y z pa pb
theorem leftPure (x) : FibreValue.Pure (payloadMap ((leftArrow (S := S) Y r).app x)) := by
  have a := joinAligned (wr (S := S) Y r) (stage (S := S) Y V) (NativeTrace.leaf (LY (S := S) Y) V.dest)
    (ContextadOuterCharts.last (S := S) Y V) (BlockEvaluation.global S Y 1) (ContextadOuterCharts.last (S := S) Y U) (prior (S := S) Y U)
    (stageLeaf (S := S) Y V) (stageLeaf (S := S) Y U).symm (leftCore (S := S) Y r) x
  exact payloadAligned (Y := LY (S := S) Y) (e := 𝟭 B) a
    (decodedChosen (S := S) Y ((gLift (S := S) Y r).app x) (pureId _) (pureId _))
theorem bothChosen (x) : Aligned ((leftArrow (S := S) Y r).app x) ((rightArrow (S := S) Y r).app x) :=
  alignChosen (LY (S := S) Y) (𝟭 B) rfl (baseAligned Y r x) (leftPure Y r x) (pureId _)
theorem stagePure (x) : FibreValue.Pure ((stageComparison (S := S) Y r).hom.app x) := by
  unfold stageComparison
  apply pureMate
  exact fun z => pureCastFactor (pr (LY (S := S) Y)) (leftArrow (S := S) Y r) (rightArrow (S := S) Y r) (congrArg (· ⋙ V.dest) (gradeEq (S := S) Y r)) (outOver (S := S) Y r) (rightCart (S := S) Y r) (bothChosen (S := S) Y r) z
end ContextualComposition.GrothendieckStep.ContextadOuterRigidity
