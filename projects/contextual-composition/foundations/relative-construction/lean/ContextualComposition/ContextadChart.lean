module
public import ContextualComposition.ContextadCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadChart
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage SpanApex TelescopeSquares ContextadCartesian
universe u v
set_option backward.isDefEq.respectTransparency false
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev G (n : Nat) := Evaluation.G S Y n
theorem verticalComparison (n : Nat) (A : B) :
    SpanPayload.Power.pack S n A Y ⋙ SpanPayload.Power.fibreInclude A Y _ _ ⋙ Evaluation.functor S Y n =
      Fibre.comparison S (n+1) A ⋙ FibreValue.incl (G S Y n) A := by
  fapply Functor.ext
  · intro _; rfl
  · intro x y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply (homEquiv _ _).injective
    refine Sigma.ext (by rfl) ?_
    have hf := FibreValue.embed_payload (G S Y n) ((Fibre.comparison S (n+1) A).map f)
    refine HEq.trans ?_ hf.symm
    change HEq (squareEquiv Y S _ _ _ _ _ f) (Fibre.homComparison S x y f)
    have cast' {C : Type u} [Category.{max u v} C] {x d e : C} (h : d = e) (m : x ⟶ d) :
        HEq m (Equiv.cast (congrArg (fun dest => x ⟶ dest) h) m) := by subst e; rfl
    exact cast' (Functor.congr_obj (congrArg Cat.Hom.toFunctor ((Iterates.layer P S Y (n+1)).map_id (op A))) _) _
abbrev one (A : B) := FibreValue.incl P.grades A
theorem oneEnd (A : B) : one (P := P) A ⋙ right P S = P.extend A := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    change (P.extend A).map (payloadMap ((one (P := P) A).map f)) ≫ (P.lift (𝟙 A)).app y = _
    have h : payloadMap ((one (P := P) A).map f) = f ≫ headId (P := P) y := by
      apply eq_of_heq
      refine HEq.trans (FibreValue.embed_payload P.grades f) ?_
      have t {C : Type u} [Category.{max u v} C] {x z d : C} (q : z = d) (m : x ⟶ z) : HEq m (m ≫ eqToHom q) := by subst d; simp
      exact t _ _
    rw [h, Functor.map_comp, Category.assoc]
    exact (congrArg ((P.extend A).map f ≫ ·) (next_id S y)).trans (Category.comp_id _)
end ContextualComposition.GrothendieckStep.ContextadChart
