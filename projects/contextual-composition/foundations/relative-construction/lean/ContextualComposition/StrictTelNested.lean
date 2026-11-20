module
public import ContextualComposition.StrictTelOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelNested
open CategoryTheory SpanApex NativeBlocks NativeBlocks.Nested
open StrictSpanAlgebra StrictTelOperations
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)

noncomputable def concatenate (m n : Nat) :
    Over (Pair (power S m) (power S n)) (power S (m+n)) :=
  let c := blocks S m n
  ⟨c.joinFunctor,c.join_source,c.join_dest⟩

variable (A : Over (whole S) (power S 1))
/-- On the (k)-th outer summand, the native Tel(a) applies a to
every actual block and targets the same outer length k. -/
noncomputable def blocksMap : (k : Nat) → Over (word S k) (power S k)
  | 0 => StrictSpanAlgebra.id _
  | 1 => A
  | k+2 => StrictSpanAlgebra.comp (both (blocksMap (k+1)) A) (concatenate S (k+1) 1)

noncomputable def map : strings S ⥤ tel S :=
  Sigma.desc fun k => (blocksMap S A k).functor ⋙ incl S k

theorem map_at (k : Nat) : outer S k ⋙ map S A = (blocksMap S A k).functor ⋙ incl S k := rfl

theorem concatenateRead (m n : Nat) :
    (concatenate S m n).functor ⋙ incl S (m+n) = tagPair S (m,n) ⋙ binary S :=
  (binary_at S m n).symm

theorem map_succ (k : Nat) :
    (blocksMap S A (k+2)).functor ⋙ incl S (k+2) =
      NativeAssoc.mul S
        (Strict.fst _ _ ⋙ (blocksMap S A (k+1)).functor ⋙ incl S (k+1))
        (Strict.snd _ _ ⋙ A.functor ⋙ incl S 1)
        ((congrArg (Strict.fst _ _ ⋙ ·) (blocksMap S A (k+1)).dest).trans
          ((Strict.commute _ _).trans (congrArg (Strict.snd _ _ ⋙ ·) A.source.symm))) := by
  let L := both (blocksMap S A (k+1)) A
  change L.functor ⋙ (concatenate S (k+1) 1).functor ⋙ incl S (k+2) = _
  rw [concatenateRead S]
  unfold NativeAssoc.mul
  exact congrArg (· ⋙ binary S) (Strict.uniq _ _ (L.functor ⋙ tagPair S (k+1,1)) _ rfl rfl)

structure Equations : Prop where
  singleton : incl S 1 ⋙ A.functor = 𝟭 _
  multiply : flatten S ⋙ A.functor = map S A ⋙ A.functor

noncomputable def readOperations : Ops (power S 1) where
  unit := ⟨incl S 0 ⋙ A.functor,congrArg (incl S 0 ⋙ ·) A.source,congrArg (incl S 0 ⋙ ·) A.dest⟩
  tensor := StrictSpanAlgebra.comp (concatenate S 1 1)
    ⟨incl S 2 ⋙ A.functor,congrArg (incl S 2 ⋙ ·) A.source,congrArg (incl S 2 ⋙ ·) A.dest⟩

theorem readTensor (h : Equations S A) :
    Multiplicative A (M := ops S) (N := readOperations S A) where
  unit := rfl
  tensor := by
    have j := congrArg (outer S 2 ⋙ ·) h.multiply
    change (outer S 2 ⋙ flatten S) ⋙ A.functor = _ at j
    rw [flatten_two S] at j
    exact j

variable (M : Ops (power S 1))

theorem preserves_flatten (s : incl S 1 ⋙ A.functor = 𝟭 _)
    (h : Multiplicative A (M := ops S) (N := M)) :
    ∀ k, (collapse S k).functor ⋙ A.functor = (blocksMap S A k).functor ⋙ incl S k ⋙ A.functor
  | 0 => rfl
  | 1 => ((Functor.comp_id _).symm.trans ((congrArg (A.functor ⋙ ·) s).symm))
  | k+2 => by
    let L := Strict.fst (word S (k+1)).dest (leftLeg S)
    let R := Strict.snd (word S (k+1)).dest (leftLeg S)
    let p := L ⋙ (collapse S (k+1)).functor
    have x : p ⋙ rightLeg S = R ⋙ leftLeg S :=
      (congrArg (L ⋙ ·) (collapse S (k+1)).dest).trans (Strict.commute _ _)
    have j := preserveJoin A h p R x
    change NativeAssoc.mul S p R x ⋙ A.functor = _
    refine j.trans ?_
    have p₀ : p ⋙ A.functor = L ⋙ (blocksMap S A (k+1)).functor ⋙ incl S (k+1) ⋙ A.functor :=
      congrArg (L ⋙ ·) (preserves_flatten s h (k+1))
    have q₀ : R ⋙ A.functor = (R ⋙ A.functor ⋙ incl S 1) ⋙ A.functor :=
      ((Functor.comp_id _).symm.trans (congrArg ((R ⋙ A.functor) ⋙ ·) s.symm))
    have m : (L ⋙ (blocksMap S A (k+1)).functor ⋙ incl S (k+1)) ⋙ rightLeg S =
      (R ⋙ A.functor ⋙ incl S 1) ⋙ leftLeg S :=
      (congrArg (L ⋙ ·) (blocksMap S A (k+1)).dest).trans
        ((Strict.commute _ _).trans (congrArg (R ⋙ ·) A.source.symm))
    have y := preserveJoin A h (L ⋙ (blocksMap S A (k+1)).functor ⋙ incl S (k+1))
      (R ⋙ A.functor ⋙ incl S 1) m
    refine (joinEq M p₀ q₀).trans (y.symm.trans ?_)
    exact congrArg (· ⋙ A.functor) (map_succ S A k).symm

theorem assemble_law (s : incl S 1 ⋙ A.functor = 𝟭 _)
    (h : Multiplicative A (M := ops S) (N := M)) : Equations S A where
  singleton := s
  multiply := by
    fapply Functor.ext
    · rintro ⟨n,x⟩; exact Functor.congr_obj (preserves_flatten S A M s h n) x
    · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (preserves_flatten S A M s h n) f

theorem foldEquations (L : Laws M) : Equations S (StrictTelFold.eval S M) :=
  assemble_law S _ M (StrictTelFold.eval_one S M) (foldMultiplicative S M L)

end ContextualComposition.GrothendieckStep.StrictTelNested
