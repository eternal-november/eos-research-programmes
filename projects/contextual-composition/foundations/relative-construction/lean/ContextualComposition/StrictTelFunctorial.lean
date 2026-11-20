module
public import ContextualComposition.StrictTelMapLaws
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelFunctorial
open CategoryTheory SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelMap
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B] {P Q R : Endpoints.{b,max b w,b,max b w} B}
variable (S : P.Split) (T : Q.Split) (U : R.Split)

theorem powerId (n : Nat) :
    powerMap S S (StrictSpanAlgebra.id _) n = StrictSpanAlgebra.id _ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      apply overExt
      apply NativeAssoc.snoc_ext S (k+1)
      · rw [map_succ_prefix S S]
        rw [ih]
        exact (Functor.comp_id _).trans (Functor.id_comp _).symm
      · rw [map_succ_suffix S S]
        exact (Functor.comp_id _).trans (Functor.id_comp _).symm

theorem powerComp (F : Over (power S 1) (power T 1)) (G : Over (power T 1) (power U 1)) (n : Nat) :
    powerMap S U (StrictSpanAlgebra.comp F G) n =
      StrictSpanAlgebra.comp (powerMap S T F n) (powerMap T U G n) := by
  induction n with
  | zero => apply overExt; exact (Functor.id_comp _).symm
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      apply overExt
      apply NativeAssoc.snoc_ext U (k+1)
      · have a := map_succ_prefix S U (StrictSpanAlgebra.comp F G) k
        have r := congrArg (fun J : Over (power S (k+1)) (power U (k+1)) =>
          NativeAssoc.front S (k+1) ⋙ J.functor) ih
        have v := congrArg ((powerMap S T F (k+2)).functor ⋙ ·) (map_succ_prefix T U G k)
        have w := congrArg (· ⋙ (powerMap T U G (k+1)).functor) (map_succ_prefix S T F k)
        exact a.trans (r.trans ((v.trans w).symm))
      · have a := map_succ_suffix S U (StrictSpanAlgebra.comp F G) k
        have v := congrArg ((powerMap S T F (k+2)).functor ⋙ ·) (map_succ_suffix T U G k)
        have w := congrArg (· ⋙ G.functor) (map_succ_suffix S T F k)
        exact a.trans ((v.trans w).symm)

theorem mapId : map S S (StrictSpanAlgebra.id _) = StrictSpanAlgebra.id _ := by
  apply overExt
  fapply Functor.ext
  · rintro ⟨n,x⟩
    have e := congrArg (fun J : Over (power S n) (power S n) => J.functor ⋙ incl S n) (powerId S n)
    exact Functor.congr_obj e x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    have e := congrArg (fun J : Over (power S n) (power S n) => J.functor ⋙ incl S n) (powerId S n)
    exact Functor.congr_hom e f

theorem mapComp (F : Over (power S 1) (power T 1)) (G : Over (power T 1) (power U 1)) :
    map S U (StrictSpanAlgebra.comp F G) = StrictSpanAlgebra.comp (map S T F) (map T U G) := by
  apply overExt
  fapply Functor.ext
  · rintro ⟨n,x⟩
    have e := congrArg (fun J : Over (power S n) (power U n) => J.functor ⋙ incl U n) (powerComp S T U F G n)
    exact Functor.congr_obj e x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    have e := congrArg (fun J : Over (power S n) (power U n) => J.functor ⋙ incl U n) (powerComp S T U F G n)
    exact Functor.congr_hom e f

end ContextualComposition.GrothendieckStep.StrictTelFunctorial
