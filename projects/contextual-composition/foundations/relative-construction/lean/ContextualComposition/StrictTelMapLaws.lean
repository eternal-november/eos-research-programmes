module
public import ContextualComposition.StrictTelMap
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelMapLaws
open CategoryTheory SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelOperations StrictTelNested StrictTelRecovery StrictTelCartesian
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000
variable {B : Type b} [Category.{max b w} B] {P Q : Endpoints.{b,max b w,b,max b w} B}
variable (S : P.Split) (T : Q.Split)
variable (F : Over (power S 1) (power T 1)) (M : Ops (power S 1)) (N : Ops (power T 1))

theorem comb_natural (h : Multiplicative F (M := M) (N := N)) (n : Nat) :
    (StrictTelFold.comb S M n).functor ⋙ F.functor =
      (StrictTelMap.powerMap S T F n).functor ⋙ (StrictTelFold.comb T N n).functor := by
  induction n with
  | zero => exact h.unit.trans (Functor.id_comp _).symm
  | succ k ih =>
    cases k with
    | zero => exact (Functor.id_comp _).trans (Functor.comp_id _).symm
    | succ k =>
      let J := (StrictTelMap.powerMap S T F (k+2)).functor
      let r := NativeAssoc.front S (k+1)
      let p := r ⋙ (StrictTelFold.comb S M (k+1)).functor
      let q := NativeAssoc.last S (k+1)
      let e : p ⋙ (power S 1).dest = q ⋙ (power S 1).source :=
        (congrArg (r ⋙ ·) (StrictTelFold.comb S M (k+1)).dest).trans (NativeAssoc.boundary S (k+1))
      have ep : p ⋙ F.functor = J ⋙ NativeAssoc.front T (k+1) ⋙ (StrictTelFold.comb T N (k+1)).functor :=
        (congrArg (r ⋙ ·) ih).trans
          (congrArg (· ⋙ (StrictTelFold.comb T N (k+1)).functor) (StrictTelMap.map_succ_prefix S T F k).symm)
      have eq : q ⋙ F.functor = J ⋙ NativeAssoc.last T (k+1) :=
        (StrictTelMap.map_succ_suffix S T F k).symm
      change join M p q e ⋙ F.functor =
        J ⋙ (StrictTelFold.snoc T N (StrictTelFold.comb T N (k+1))).functor
      exact (preserveJoin F h p q e).trans
        ((joinEq N ep eq).trans (join_before N J _ _ _).symm)

theorem eval_natural (h : Multiplicative F (M := M) (N := N)) :
    (StrictTelFold.eval S M).functor ⋙ F.functor =
      (StrictTelMap.map S T F).functor ⋙ (StrictTelFold.eval T N).functor := by
  fapply Functor.ext
  · rintro ⟨n,x⟩; exact Functor.congr_obj (comb_natural S T F M N h n) x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (comb_natural S T F M N h n) f

variable (A : Over (whole S) (power S 1)) (D : Over (whole T) (power T 1))
/-- The strict algebra-map equation is on the literal tagged Tel functor.
There is no chosen comparison cell in this interface. -/
def AlgebraMap : Prop := A.functor ⋙ F.functor = (StrictTelMap.map S T F).functor ⋙ D.functor

theorem map_read (h : AlgebraMap S T F A D) :
    Multiplicative F (M := readOperations S A) (N := readOperations T D) where
  unit := by
    refine (congrArg (incl S 0 ⋙ ·) h).trans ?_
    change (𝟭 B) ⋙ (incl T 0 ⋙ D.functor) = incl T 0 ⋙ D.functor
    exact Functor.id_comp _
  tensor := by
    have y := congrArg ((concatenate S 1 1).functor ⋙ incl S 2 ⋙ ·) h
    change _ = (((concatenate S 1 1).functor ⋙ (cutLast S 1).functor) ⋙
      (both F F).functor ⋙ (concatenate T 1 1).functor ⋙ incl T 2 ⋙ D.functor) at y
    refine y.trans ?_
    rw [StrictTelMap.glue_cut S 1,Functor.id_comp]
    rfl

theorem map_iff (a : Equations S A) (d : Equations T D) :
    AlgebraMap S T F A D ↔ Multiplicative F (M := readOperations S A) (N := readOperations T D) := by
  constructor
  · exact map_read S T F A D
  · intro h
    have a₀ := unique S A _ (recoveredLaws S A a) a.singleton (readTensor S A a)
    have d₀ := unique T D _ (recoveredLaws T D d) d.singleton (readTensor T D d)
    change A.functor ⋙ F.functor = (StrictTelMap.map S T F).functor ⋙ D.functor
    exact (congrArg (fun f => f.functor ⋙ F.functor) a₀).trans
      ((eval_natural S T F _ _ h).trans (congrArg (fun f => (StrictTelMap.map S T F).functor ⋙ f.functor) d₀.symm))

end ContextualComposition.GrothendieckStep.StrictTelMapLaws
