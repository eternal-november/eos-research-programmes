module
public import ContextualComposition.ContextadInsideCharts
public import ContextualComposition.ContextadPayloadModification
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadChartDescent
open CategoryTheory CategoryTheory.Functor Opposite ContextadLawTransport FibreValue
universe u v
section General
variable {C₀ C₁ C₂ D₀ D₁ D₂ B : Type*}
  [Category* C₀] [Category* C₁] [Category* C₂] [Category* D₀] [Category* D₁] [Category* D₂] [Category* B]
variable (p : C₀ ⥤ C₁) (q : D₀ ⥤ D₁) (U : C₀ ⥤ C₂) (V : D₀ ⥤ D₂)
    (J : C₁ ⥤ C₂) (K : D₁ ⥤ D₂) [U.IsIso] [J.IsIso]
    (r : C₀ ⥤ D₀) (t : C₁ ⥤ D₁)
    (a : p ⋙ J = U) (b : q ⋙ K = V) (i : r ⋙ q ≅ p ⋙ t)
include a in
theorem erase : U.strictInv ⋙ p = J.strictInv := by
  apply J.asIsomorphism.comp_functor_injective
  exact (congrArg (U.strictInv ⋙ ·) a).trans (U.asIsomorphism.counit_eq.trans J.asIsomorphism.counit_eq.symm)
noncomputable def chartIso : U.strictInv ⋙ r ⋙ V ≅ J.strictInv ⋙ t ⋙ K :=
  eqToIso (congrArg (U.strictInv ⋙ r ⋙ ·) b.symm) ≪≫
    isoWhiskerLeft U.strictInv (isoWhiskerRight i K) ≪≫
    eqToIso (congrArg (· ⋙ t ⋙ K) (erase p U J a))
theorem chartPure (π : D₂ ⥤ B) (v : ∀ x, Pure ((K ⋙ π).map (i.hom.app x))) (x : C₂) :
    Pure (π.map ((chartIso p q U V J K r t a b i).hom.app x)) :=
  castPure π _ _ (isoWhiskerLeft U.strictInv (isoWhiskerRight i K)) (fun z => v (U.strictInv.obj z)) x
end General
variable {B : Type u} [Category.{max u v} B]
variable {G H : Bᵒᵖ ⥤ Cat.{max u v,u}}
noncomputable def localIso (F J : Total G (𝟭 B) ⥤ Total H (𝟭 B)) (f : F ⋙ proj H = proj G) (j : J ⋙ proj H = proj G)
    (i : F ≅ J) (v : ∀ x, Pure ((proj H).map (i.hom.app x))) (A : B) :
    ContextadTotal.localValue G H F f A ≅ ContextadTotal.localValue G H J j A :=
  isoWhiskerLeft (embed G A) (isoWhiskerRight (onFiber F J f j i v A) (value H A))
end ContextualComposition.GrothendieckStep.ContextadChartDescent
