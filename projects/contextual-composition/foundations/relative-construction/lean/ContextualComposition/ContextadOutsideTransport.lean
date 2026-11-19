module
public import ContextualComposition.ContextadOuterRigidity
public import ContextualComposition.ContextadCellPasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadOuterRigidity
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadOuterCharts ContextadRoutes ContextadLawTransport ContextadChartDescent ContextadNativeLaws
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
universe u v
variable {X D : Type*} [Category* X] [Category* D] {F G : X ⥤ D}
theorem functorRigid (i : F ≅ G) (p : ∀ x, Pure (i.hom.app x)) : F = G :=
  Functor.ext_of_iso i (fun x => (p x).choose) fun x => (p x).choose_spec
theorem isoRigid (i : F ≅ G) (p : ∀ x, Pure (i.hom.app x)) : i = eqToIso (functorRigid i p) := by
  apply Iso.ext; apply NatTrans.ext; funext x
  rw [eqToIso.hom,eqToHom_app]
  exact (p x).choose_spec
theorem alignTransports {x y x' y' : D} {f : x ⟶ y} {g : x' ⟶ y'} (s : x=x') (p : Pure f) (q : Pure g) : Aligned f g := by
  obtain ⟨rfl,rfl⟩ := p; obtain ⟨rfl,rfl⟩ := q; cases s; exact Aligned.refl _
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
theorem outsideUnitTransport (d : ContextadUnit.Data P) (x) : Pure ((outerUnitTotal (S := S) Y d).hom.app x) := by
  let _ : (BlockEvaluation.global S Y (0+1)).IsIso := BlockEvaluation.globalIso S Y (0+1)
  let _ : (BlockEvaluation.global S (LY (S := S) Y) 0).IsIso := BlockEvaluation.globalIso S (LY (S := S) Y) 0
  exact chartPure (stage (S := S) Y (power S 0)) (stage (S := S) Y (power S 1))
    (BlockEvaluation.global S Y (0+1)) (BlockEvaluation.global S Y (1+1)) (BlockEvaluation.global S (LY (S := S) Y) 0)
    (BlockEvaluation.global S (LY (S := S) Y) 1) _ _ (resolve0 (S := S) Y) (resolve1 (S := S) Y)
    (stageComparison (S := S) Y (insert S d)) (𝟭 _) (fun w => pureMap _ (stagePure (S := S) Y (insert S d) w)) x
theorem outsideTensorTransport (m : ContextadTotal.Native S) (x) : Pure ((outerTensorTotal Y m).hom.app x) := by
  let _ : (BlockEvaluation.global S Y (2+1)).IsIso := BlockEvaluation.globalIso S Y (2+1)
  let _ : (BlockEvaluation.global S (LY (S := S) Y) 2).IsIso := BlockEvaluation.globalIso S (LY (S := S) Y) 2
  exact chartPure (stage (S := S) Y (power S 2)) (stage (S := S) Y (power S 1))
    (BlockEvaluation.global S Y (2+1)) (BlockEvaluation.global S Y (1+1)) (BlockEvaluation.global S (LY (S := S) Y) 2)
    (BlockEvaluation.global S (LY (S := S) Y) 1) _ _ (resolve2 (S := S) Y) (resolve1 (S := S) Y)
    (stageComparison (S := S) Y (tensor m)) (𝟭 _) (fun w => pureMap _ (stagePure (S := S) Y (tensor m) w)) x
section Local
variable {G H : Bᵒᵖ ⥤ Cat.{max u v,u}} (F J : Total G (𝟭 B) ⥤ Total H (𝟭 B))
    (f : F ⋙ proj H = proj G) (j : J ⋙ proj H = proj G) (i : F ≅ J) (v : ∀ x, Pure ((proj H).map (i.hom.app x)))
theorem localTransport (p : ∀ x, Pure (i.hom.app x)) (A : B) (x) :
    Pure ((localIso F J f j i v A).hom.app x) := by
  let n := (onFiber F J f j i v A).hom.app ((embed G A).obj x)
  apply pureMap (value H A)
  apply ContextadCoherence.fibrePure H n
  apply payloadAligned (ContextadModification.fibreAligned F J f j i v A _)
  obtain ⟨e,h⟩ := p (((embed G A).obj x).val)
  rw [h]; exact ContextadPayloadModification.pureCast _ _
end Local
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (A : B)
theorem afterTransport {C D : Type*} [Category* C] [Category* D] {F G H : C ⥤ D}
    (i : F ≅ G) (k : G=H) (p : ∀ x, Pure (i.hom.app x)) (x : C) : Pure ((i ≪≫ eqToIso k).hom.app x) :=
  pureComp (p x) ⟨_,eqToHom_app k x⟩
theorem localWithCast {G H : Bᵒᵖ ⥤ Cat.{max u v,u}} (F J : Total G (𝟭 B) ⥤ Total H (𝟭 B))
    (f : F ⋙ proj H = proj G) (j : J ⋙ proj H = proj G) (i : F ≅ J) (v : ∀ x, Pure ((proj H).map (i.hom.app x)))
    (p : ∀ x, Pure (i.hom.app x)) (A : B) {K : G.obj (op A) ⥤ H.obj (op A)} (k : ContextadTotal.localValue G H J j A = K) (x : G.obj (op A)) :
    Pure ((localIso F J f j i v A ≪≫ eqToIso k).hom.app x) :=
  afterTransport (localIso F J f j i v A) k (localTransport F J f j i v p A) x
end ContextualComposition.GrothendieckStep.ContextadOuterRigidity
