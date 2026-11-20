module
public import ContextualComposition.StrictTelAlgebra
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelMap
open CategoryTheory SpanApex NativeBlocks NativeCleavage
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictSpanCart StrictTelOperations StrictTelNested StrictTelRecovery StrictTelCartesian
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B] {P Q : Endpoints.{b,max b w,b,max b w} B}
variable (S : P.Split) (T : Q.Split)

theorem glue_prefix (n : Nat) :
    (concatenate S n 1).functor ⋙ NativeAssoc.front S n = Strict.fst (power S n).dest (power S 1).source := by
  let p : NativeAssoc.Path S (Pair (power S n) (power S 1)).apex := ⟨n,Strict.fst _ _⟩
  let G := Strict.snd (power S n).dest (power S 1).source
  let h : NativeAssoc.dst S p = G ⋙ left P := Strict.commute _ _
  have j : (NativeAssoc.join S p (single S G) h).2 = (NativeAssoc.grow S p G h).2 :=
    eq_of_heq (Sigma.ext_iff.mp (joinSingle S p G h)).2
  have z := congrArg (· ⋙ NativeAssoc.front S n) j
  exact z.trans (NativeAssoc.grow_pre S p G h)

theorem glue_suffix (n : Nat) :
    (concatenate S n 1).functor ⋙ NativeAssoc.last S n = Strict.snd (power S n).dest (power S 1).source := by
  let p : NativeAssoc.Path S (Pair (power S n) (power S 1)).apex := ⟨n,Strict.fst _ _⟩
  let G := Strict.snd (power S n).dest (power S 1).source
  let h : NativeAssoc.dst S p = G ⋙ left P := Strict.commute _ _
  have j : (NativeAssoc.join S p (single S G) h).2 = (NativeAssoc.grow S p G h).2 :=
    eq_of_heq (Sigma.ext_iff.mp (joinSingle S p G h)).2
  exact (congrArg (· ⋙ NativeAssoc.last S n) j).trans (NativeAssoc.grow_last S p G h)

theorem glue_cut (n : Nat) :
    (concatenate S n 1).functor ⋙ (cutLast S n).functor = 𝟭 _ :=
  Strict.uniq _ _ _ _ (glue_prefix S n) (glue_suffix S n)

variable (F : Over (power S 1) (power T 1))
/-- Strict on both legs. On directed squares this is the actual tensor
power of F: it applies F to each native primitive arrow, with no inverse. -/
noncomputable def powerMap : (n : Nat) → Over (power S n) (power T n)
  | 0 => StrictSpanAlgebra.id _
  | 1 => F
  | k+2 => StrictSpanAlgebra.comp
      (StrictSpanAlgebra.comp (cutLast S (k+1)) (both (powerMap (k+1)) F))
        (concatenate T (k+1) 1)

noncomputable def map : Over (whole S) (whole T) where
  functor := Sigma.desc fun n => (powerMap S T F n).functor ⋙ incl T n
  source := by
    fapply Functor.ext
    · rintro ⟨n,x⟩; exact Functor.congr_obj (powerMap S T F n).source x
    · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (powerMap S T F n).source f
  dest := by
    fapply Functor.ext
    · rintro ⟨n,x⟩; exact Functor.congr_obj (powerMap S T F n).dest x
    · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (powerMap S T F n).dest f

theorem map_at (n : Nat) :
    incl S n ⋙ (map S T F).functor = (powerMap S T F n).functor ⋙ incl T n := rfl

theorem map_succ_prefix (k : Nat) :
    (powerMap S T F (k+2)).functor ⋙ NativeAssoc.front T (k+1) =
      NativeAssoc.front S (k+1) ⋙ (powerMap S T F (k+1)).functor := by
  change (cutLast S (k+1)).functor ⋙ (both (powerMap S T F (k+1)) F).functor ⋙
    ((concatenate T (k+1) 1).functor ⋙ NativeAssoc.front T (k+1)) = _
  rw [glue_prefix T]
  rfl

theorem map_succ_suffix (k : Nat) :
    (powerMap S T F (k+2)).functor ⋙ NativeAssoc.last T (k+1) =
      NativeAssoc.last S (k+1) ⋙ F.functor := by
  change (cutLast S (k+1)).functor ⋙ (both (powerMap S T F (k+1)) F).functor ⋙
    ((concatenate T (k+1) 1).functor ⋙ NativeAssoc.last T (k+1)) = _
  rw [glue_suffix T]
  rfl

theorem powerCart (h : CartesianMap F) (n : Nat) : CartesianMap (powerMap S T F n) := by
  induction n with
  | zero => exact identity _
  | succ k ih =>
    cases k with
    | zero => exact h
    | succ k =>
      exact compose (compose (isomorphism (cutLast S (k+1)))
        (bothCart (SpanPull.All.parts S (k+1)) (SpanPull.All.parts S 1) ih h)) (joinCart T (k+1) 1)

theorem mapCart (h : CartesianMap F) : CartesianMap (map S T F) := by
  intro x y f hf
  obtain ⟨n,x⟩ := x; obtain ⟨j,y⟩ := y
  cases f with
  | mk f =>
    have k := (BlockCartesian.cartesian_iff (incl S n) (BlockCartesian.inclIncoming n) (leftLeg S) f).mpr hf
    exact tagCart T n _ (powerCart S T F h n f k)

end ContextualComposition.GrothendieckStep.StrictTelMap
