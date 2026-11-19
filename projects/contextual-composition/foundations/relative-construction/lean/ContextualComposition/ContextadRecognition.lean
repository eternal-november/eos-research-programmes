module
public import ContextualComposition.ContextadVertical
public import ContextualComposition.WordTrace
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadRecognition
open TelescopeSquares CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanApex NativeBlocks BlockEvaluation ContextadVertical SpanPayload.Power
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem cancelFull (Q : C ⥤ D) [Q.Full] (surj : Function.Surjective Q.obj) (F G : D ⥤ E)
    (h : Q ⋙ F = Q ⋙ G) : F = G := by
  apply WordTrace.Edge.functor_ext
  rintro ⟨x,y,f⟩
  obtain ⟨x,rfl⟩ := surj x
  obtain ⟨y,rfl⟩ := surj y
  obtain ⟨g,rfl⟩ := Q.map_surjective f
  exact congrArg (fun J => WordTrace.Edge.map J ⟨x,y,g⟩) h
theorem genericIncl {B : Type*} [Category* B] (G H : Bᵒᵖ ⥤ Cat.{v,u}) (A : B)
    (F : Total G (𝟭 B) ⥤ Total H (𝟭 B)) (h : F ⋙ FibreValue.proj H = FibreValue.proj G) :
    ContextadTotal.localValue G H F h A ⋙ FibreValue.incl H A = FibreValue.incl G A ⋙ F := by
  let E := FibreValue.embed G A
  let J := SpanPayload.fibreFunctor F _ h A
  let I := Functor.Fiber.fiberInclusion (p := FibreValue.proj H) (S := A)
  exact (congrArg (fun U => E ⋙ J ⋙ U ⋙ I) (FibreValue.value_embed H A)).trans
    (congrArg (E ⋙ ·) (SpanPayload.fibre_diagram F _ h A))
theorem eraseInv (F : C ⥤ D) [F.IsIso] (H : C ⥤ E) : F ⋙ (F.strictInv ⋙ H) = H :=
  congrArg (· ⋙ H) F.asIsomorphism.unit_eq.symm
theorem paste4 {C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₅] [Category* C₆] [Category* C₇]
    (Q : C₀ ⥤ C₁) (T : C₁ ⥤ C₂) (U : C₂ ⥤ C₃) (G : C₃ ⥤ C₄) (L : C₂ ⥤ C₄)
    (V : C₀ ⥤ C₅) (M : C₅ ⥤ C₃) (K : C₅ ⥤ C₆) (N : C₆ ⥤ C₄) (I : C₁ ⥤ C₇) (W : C₇ ⥤ C₆)
    (u : U ⋙ G = L) (a : V ⋙ M = Q ⋙ T ⋙ U) (b : K ⋙ N = M ⋙ G) (c : Q ⋙ I ⋙ W = V ⋙ K) :
    Q ⋙ T ⋙ L = Q ⋙ I ⋙ W ⋙ N :=
  (congrArg (Q ⋙ T ⋙ ·) u.symm).trans ((congrArg (· ⋙ G) a.symm).trans ((congrArg (V ⋙ ·) b.symm).trans (congrArg (· ⋙ N) c.symm)))
theorem postSquare {A B C D E : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (q : A ⥤ B) (i : B ⥤ D) (v : A ⥤ C) (g : C ⥤ D) (e : D ⥤ E) (j : C ⥤ E)
    (p : q ⋙ i = v ⋙ g) (h : g ⋙ e = j) : q ⋙ i ⋙ e = v ⋙ j :=
  (congrArg (· ⋙ e) p).trans (congrArg (v ⋙ ·) h)
theorem finish {A B C D E F G : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F] [Category* G]
    (q : A ⥤ B) (old : B ⥤ C) (l : C ⥤ D) (pack : A ⥤ E) (t : E ⥤ C) (i : E ⥤ F) (e : F ⥤ G) (n : G ⥤ D) (inc : B ⥤ G)
    (r : q ⋙ old = pack ⋙ t) (b : t ⋙ l = i ⋙ e ⋙ n) (v : pack ⋙ i ⋙ e = q ⋙ inc) :
    q ⋙ old ⋙ l = q ⋙ inc ⋙ n :=
  (congrArg (· ⋙ l) r).trans ((congrArg (pack ⋙ ·) b).trans (congrArg (· ⋙ n) v))
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (m : ContextadTotal.Native S) (d : ContextadTensor.Data S) (A : B) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
noncomputable abbrev old := ContextadTensor.binary d Y A
abbrev incl (n : Nat) := FibreValue.incl (PackedFree.pow S Y n) A
theorem localIncl : ContextadTotal.binary m Y A ⋙ incl (S := S) A Y 1 = incl (S := S) A Y 2 ⋙ ContextadTotal.total m Y :=
  genericIncl _ _ A _ (ContextadTotal.totalOver m Y)
theorem inputPaste :
    weighted S 1 A Y ⋙ fibreInclude A Y (chainSource S 1) (chainDest S 1) ⋙ Evaluation.functor S Y 1 =
    fibreInclude A Y (power S 2).source (power S 2).dest ⋙ BlockEvaluation.global S Y 2 :=
  postSquare _ _ _ (SpanPayload.Power.global S 1 Y) (Evaluation.functor S Y 1) (BlockEvaluation.global S Y 2)
    (fibre_global S 1 A Y) rfl
theorem actionPaste :
    BlockEvaluation.global S Y 2 ⋙ ContextadTotal.total m Y = ContextadTotal.action m Y ⋙ BlockEvaluation.global S Y 1 :=
  eraseInv (BlockEvaluation.global S Y 2) (ContextadTotal.action m Y ⋙ BlockEvaluation.global S Y 1)
theorem chartRecognition (h : Agrees m d A)
    (unary : insertOne (S := S) A Y ⋙ global S Y 1 = incl (S := S) A Y 1) :
    old d A Y ⋙ incl (S := S) A Y 1 = incl (S := S) A Y 2 ⋙ ContextadTotal.total m Y := by
  apply (Fibre.comparison (Y := Y) S 2 A).asIsomorphism.functor_comp_injective
  let Q := weighted S 1 A Y
  let V := fibreInclude A Y (power S 2).source (power S 2).dest
  let I := fibreInclude A Y (chainSource S 1) (chainDest S 1)
  let T := restrict Y _ _ (d.tensor A) (d.delta A)
  let L := incl (S := S) A Y 1
  have t : T ⋙ L = I ⋙ Evaluation.functor S Y 1 ⋙ ContextadTotal.total m Y := by
    apply cancelFull Q (SpanPayload.total_obj_surjective _ _ _ (SpanPayload.fibre_obj_surjective _ _ _ _ (powerPoints S 1).decode.surjective))
    have a := weightedVertical m d A Y h
    have c := actionPaste m Y
    have b' := inputPaste (S := S) A Y
    exact paste4 Q T (insertOne (S := S) A Y) (global S Y 1) L V (ContextadTotal.action m Y)
      (global S Y 2) (ContextadTotal.total m Y) I (Evaluation.functor S Y 1) unary a c b'

  exact finish (Fibre.comparison S 2 A) (old d A Y) L (pack S 1 A Y) T I (Evaluation.functor S Y 1)
    (ContextadTotal.total m Y) (incl (S := S) A Y 2) (ContextadTensor.read d Y A) t (ContextadChart.verticalComparison S Y 1 A)
end ContextualComposition.GrothendieckStep.ContextadRecognition
