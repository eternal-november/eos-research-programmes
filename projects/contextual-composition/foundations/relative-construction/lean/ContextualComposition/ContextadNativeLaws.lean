module
public import ContextualComposition.ContextadLawTransport
public import ContextualComposition.ContextadMixed
public import ContextualComposition.ContextadStrong
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadNativeLaws
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex FibreValue ContextadRoutes ContextadLawTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (d : ContextadUnit.Data P)
def unitGrade : B ⥤ Apex P where
  obj A := pair _ _ A (d.grade A)
  map f := arrow f (eqToHom (d.reindex f).symm)
  map_id A := WeightedCells.pureArrowEq _ _ rfl ⟨(d.reindex (𝟙 A)).symm,rfl⟩ (WeightedCells.totalPureId _ _ _)
  map_comp f g := WeightedCells.pureArrowEq _ _ rfl ⟨(d.reindex (f ≫ g)).symm,rfl⟩
    (WeightedCells.totalPureComp _ _ ⟨(d.reindex f).symm,rfl⟩ ⟨(d.reindex g).symm,rfl⟩)
def discharge : unitGrade d ⋙ (power S 1).dest ⟶ 𝟭 B where
  app A := d.discharge A
  naturality A D f := by
    change ((P.extend A).map (eqToHom (d.reindex f).symm) ≫ (P.lift f).app (d.grade D)) ≫ d.discharge D = _
    rw [Category.assoc,d.square f,← Category.assoc,← Functor.map_comp,eqToHom_trans,eqToHom_refl,Functor.map_id,Category.id_comp]
    rfl
def insert : Map S 0 1 := ⟨unitGrade d,rfl,discharge S d⟩
variable {S} (m : ContextadTotal.Native S)
/-- Actual native paths, not packed-word flattening. For the outside route the
following grade is reindexed by discharge or tensor comparison before contraction. -/
noncomputable abbrev leftUnit := suffix (insert S d)
noncomputable abbrev rightUnit := inside 1 (insert S d)
noncomputable abbrev firstTwo := suffix (tensor m)
noncomputable abbrev lastTwo := inside 1 (tensor m)
/-- The extra input consists of native vertical grade isomorphisms (natural on
all apex arrows) and endpoint triangles. These three cells have no payload
parameter, and are not themselves assumed to form a coherent contextad. -/
structure Constraints where
  left : Cell (comp (leftUnit d) (tensor m)) (identity 1)
  right : Cell (comp (rightUnit d) (tensor m)) (identity 1)
  assoc : Cell (comp (firstTwo m) (tensor m)) (comp (lastTwo m) (tensor m))
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) (A : B)
theorem includeUnitGrade :
    ContextadUnit.atGrade Y (P.extend A) (d.grade A) ⋙ ContextadVertical.insertOne (S := S) A Y =
      ContextadUnit.atGrade Y (right P S) ((unitGrade d).obj A) := by
  unfold ContextadVertical.insertOne
  rw [ContextadVertical.strictWeight,ContextadUnit.inclRestrict,eqToHom_app]
  change (Y.map (𝟙 _)).toFunctor ⋙ _ = _
  rw [Y.map_id]; rfl
theorem unitInto :
    ContextadUnit.atBase d Y A ⋙ ContextadVertical.insertOne (S := S) A Y =
    incl Y A ⋙ raw Y (insert S d) :=
  (congrArg ((Y.map (d.discharge A).op).toFunctor ⋙ ·) (includeUnitGrade (S := S) d Y A)).trans
    (ContextadUnit.inclRestrict Y _ _ (unitGrade d) (discharge S d) A).symm
theorem unaryPaste {C D E F G : Type*} [Category* C] [Category* D] [Category* E] [Category* F] [Category* G]
    (I : C ⥤ D) (R : D ⥤ E) (J : E ⥤ F) (T : D ⥤ F) (U : C ⥤ G) (K : G ⥤ E) (V : G ⥤ F)
    (e : T = R ⋙ J) (k : U ⋙ K = I ⋙ R) (h : K ⋙ J = V) : I ⋙ T = U ⋙ V :=
  (congrArg (I ⋙ ·) e).trans ((congrArg (· ⋙ J) k.symm).trans (congrArg (U ⋙ ·) h))
theorem evalUnit : evaluate Y (insert S d) A = ContextadUnit.atBase d Y A := by
  apply ContextadFinal.cancelIncl (PackedFree.pow S Y 1) A
  refine (evalIncl Y _ A).trans ?_
  let I := incl Y A
  let J := BlockEvaluation.global S Y 1
  have inv0 : (BlockEvaluation.global S Y 0).strictInv = 𝟭 _ :=
    (Functor.id_comp _).symm.trans (BlockEvaluation.global S Y 0).asIsomorphism.unit_eq.symm
  have erase : global Y (insert S d) = raw Y (insert S d) ⋙ J :=
    (congrArg (· ⋙ (raw Y (insert S d) ⋙ J)) inv0).trans (Functor.id_comp _)
  exact unaryPaste I (raw Y (insert S d)) J (global Y (insert S d))
    (ContextadUnit.atBase d Y A) (ContextadVertical.insertOne (S := S) A Y) (incl (PackedFree.pow S Y 1) A)
    erase (unitInto (S := S) d Y A) (ContextadUnary.recognition S A Y)
theorem result {i : Nat} (r : Map S i 2) :
    evaluate Y r A ⋙ ContextadCoherence.actual m Y A = evaluate Y (comp r (tensor m)) A :=
  (congrArg (evaluate Y r A ⋙ ·) (evalTensor Y m A).symm).trans (evalComp Y _ _ A)
variable (c : Constraints d m)
noncomputable def leftUnitor : evaluate Y (leftUnit d) A ⋙ ContextadCoherence.actual m Y A ≅ 𝟭 _ :=
  eqToIso (result m Y A _) ≪≫ evalCell Y c.left A ≪≫ eqToIso (evalId Y 1 A)
noncomputable def rightUnitor : evaluate Y (rightUnit d) A ⋙ ContextadCoherence.actual m Y A ≅ 𝟭 _ :=
  eqToIso (result m Y A _) ≪≫ evalCell Y c.right A ≪≫ eqToIso (evalId Y 1 A)
noncomputable def associator :
    evaluate Y (firstTwo m) A ⋙ ContextadCoherence.actual m Y A ≅
      evaluate Y (lastTwo m) A ⋙ ContextadCoherence.actual m Y A :=
  eqToIso (result m Y A _) ≪≫ evalCell Y c.assoc A ≪≫ eqToIso (result m Y A _).symm
end ContextualComposition.GrothendieckStep.ContextadNativeLaws
