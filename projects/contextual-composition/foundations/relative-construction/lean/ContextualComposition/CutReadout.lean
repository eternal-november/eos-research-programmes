module
public import ContextualComposition.TaggedCorner
public import ContextualComposition.CheckedCut
public import ContextualComposition.CutPayload
@[expose] public section
namespace ContextualComposition.GrothendieckStep.CutReadout
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation WholeEvaluator ChartRealization CutFold TaggedTripleFaces
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
section
variable {A B C D E F G H : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F] [Category* G] [Category* H]
theorem joinRows (t : A ⥤ B) (p : B ⥤ C) (q : C ⥤ D) (a : A ⥤ E) (b : E ⥤ F) (c : F ⥤ C)
    (k : F ⥤ D) (l : E ⥤ G) (w : G ⥤ D) (i : t ⋙ p = a ⋙ b ⋙ c) (j : c ⋙ q = k) (v : b ⋙ k = l ⋙ w) :
    t ⋙ p ⋙ q = (a ⋙ l) ⋙ w := by rw [← Functor.assoc,i,Functor.assoc,Functor.assoc,j,v,Functor.assoc]
end
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m : Nat)
theorem matched : pairTag S Y n m ⋙ binaryStages S Y = totalStages S Y n m ⋙ push S Y (n,m) :=
  joinRows (pairTag S Y n m) (dropInner S Y) (evaluate S (one S Y)) (suffix S Y n m) (innerInc S Y n m) (endTag S Y n)
    (branch S (one S Y) n) (global S (out S Y m) n) (push S Y (n,m)) (cutSuffix S Y n m) (WholeEvaluator.tagged S (one S Y) n) (CutPayload.branchMap S Y n m)
theorem readout (i : Nat × Nat) : CutRead S Y i := by
  have k := SpanPayload.total_comp Y (cut S i).functor _ (cut S i).dest (NativePacked.tagged S i).functor _ (NativePacked.tagged S i).dest
  exact (congrArg (· ⋙ binaryStages S Y) k.symm).trans (congrArg (Lift.total (cut S i) Y ⋙ ·) (matched S Y i.1 i.2))
noncomputable def bridge := stageBridge S Y (readout S Y)
end ContextualComposition.GrothendieckStep.CutReadout
