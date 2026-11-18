module
public import ContextualComposition.ChartRealization
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ChartTotalCell
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization
section General
variable {C D E H J M : Type*} [Category* C] [Category* D] [Category* E] [Category* H] [Category* J] [Category* M]
theorem pasteIncl (a : C ⥤ D) (b : D ⥤ E) (e : E ⥤ H) (p : H ⥤ J) (f : D ⥤ M) (g : M ⥤ H)
    (t : C ⥤ M) (h : b ⋙ e = f ⋙ g) (k : a ⋙ f = t) : (a ⋙ b) ⋙ e ⋙ p = t ⋙ g ⋙ p :=
  (congrArg (fun z => a ⋙ z ⋙ p) h).trans (congrArg (· ⋙ g ⋙ p) k)
theorem cell_eq {F G : C ⥤ D} (e : F = G) (K : D ⥤ E) (U : C ⥤ H) {L R : H ⥤ E} (r : L = R)
    (l : F ⋙ K = U ⋙ L) (t : G ⋙ K = U ⋙ R) :
    whiskerRight (eqToHom e) K = eqToHom l ≫ whiskerLeft U (eqToHom r) ≫ eqToHom t.symm := by
  subst G; subst R
  ext x; simp
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (A : B) (i : Nat × Nat)
abbrev I := FibreValue.incl (twice S Y) A
noncomputable abbrev K := pack S Y A i ⋙ I S Y A
theorem packedIncl :
    K S Y A i = FibreValue.incl (family S Y i.1 i.2) A ⋙ push S Y i := by
  have h := congrArg Functor.rightOp (EvalPayload.inclMapEq (ChainPayload.cell (put S Y i) (𝟭 B)) (op A))
  exact h.symm
theorem firstIncl :
    first S Y A i ⋙ K S Y A i = source S Y A i ⋙ refL S Y i := by
  rw [packedIncl]
  have k := pasteIncl (cutEach S Y A i) (staged S Y A i).functor (FibreValue.incl (family S Y i.1 i.2) A)
    (push S Y i) (SpanPayload.Power.fibreInclude A Y (fixed S i).source (fixed S i).dest)
    (totalStages S Y i.1 i.2) (source S Y A i ⋙ Lift.total (cut S i) Y) (stagedIncl S Y A i) (Lift.global (cut S i) Y A)
  exact k
theorem secondIncl :
    second S Y A i ⋙ K S Y A i = source S Y A i ⋙ refR S Y i := by
  rw [packedIncl]
  exact (congrArg (fun z => (leaf S Y A i).functor ⋙ z ⋙ push S Y i) (transportIncl A (sameLength S Y i).symm)).trans
    (congrArg (· ⋙ BlockCompositor.transport (sameLength S Y i).symm ⋙ push S Y i) (leafIncl S Y A i))
theorem restriction :
    whiskerRight (eqToHom (BlockCompositor.fixedCompositor S Y A i.1 i.2)) (K S Y A i) =
      eqToHom (firstIncl S Y A i) ≫ whiskerLeft (source S Y A i) (eqToHom (reference S Y i)) ≫ eqToHom (secondIncl S Y A i).symm := by
  exact cell_eq (BlockCompositor.fixedCompositor S Y A i.1 i.2) (K S Y A i) (source S Y A i) (reference S Y i) (firstIncl S Y A i) (secondIncl S Y A i)
end ContextualComposition.GrothendieckStep.ChartTotalCell
