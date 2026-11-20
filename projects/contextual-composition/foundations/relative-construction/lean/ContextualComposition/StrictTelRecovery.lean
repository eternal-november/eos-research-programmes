module
public import ContextualComposition.StrictTelNested
public import ContextualComposition.StrictSpanReflection
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelRecovery
open CategoryTheory SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole)
open StrictSpanAlgebra StrictTelOperations StrictTelNested
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)

theorem recoveredLaws (A : Over (whole S) (power S 1)) (h : Equations S A) :
    Laws (readOperations S A) :=
  StrictSpanReflection.reflect A (generator S) h.singleton (readTensor S A h) (strict S)

variable {X : Type b} [Category.{max b w} X]

def single (G : X ⥤ Apex P) : NativeAssoc.Path S X := ⟨1,G⟩

theorem joinSingle (p : NativeAssoc.Path S X) (G : X ⥤ Apex P) (h : NativeAssoc.dst S p = G ⋙ left P) :
    NativeAssoc.join S p (single S G) h = NativeAssoc.grow S p G h := by
  apply congrArg (Sigma.mk (p.1+1))
  apply NativeAssoc.snoc_ext S
  · refine (NativeAssoc.join_pre S p.1 0 p.2 G h).trans ?_
    have k := (blocks S p.1 0).first_assemble p.2 (G ⋙ NativeAssoc.front S 0) h
    change (blocks S p.1 0).assemble p.2 (G ⋙ NativeAssoc.front S 0) _ ⋙ 𝟭 _ = p.2 at k
    exact ((Functor.comp_id _).symm.trans k).trans (NativeAssoc.grow_pre S p G h).symm
  · exact (NativeAssoc.join_last S p.1 0 p.2 G h).trans
      ((Functor.comp_id _).trans (NativeAssoc.grow_last S p G h).symm)

variable (A : Over (whole S) (power S 1)) (M : Ops (power S 1)) (L : Laws M)
variable (s : incl S 1 ⋙ A.functor = 𝟭 _) (h : Multiplicative A (M := ops S) (N := M))

include L s h in
theorem uniquePath (p : NativeAssoc.Path S X) :
    NativeAssoc.tagged S p ⋙ A.functor = StrictTelFold.read S M p := by
  apply NativeAssoc.pathInd S (M := fun p => NativeAssoc.tagged S p ⋙ A.functor = StrictTelFold.read S M p) _ _ p
  · intro A₀; exact congrArg (A₀ ⋙ ·) h.unit
  · intro p G e ih
    have j := NativeAssoc.tag_join S p (single S G) e
    have q : (G ⋙ incl S 1) ⋙ A.functor = G :=
      (congrArg (G ⋙ ·) s).trans (Functor.comp_id _)
    have r := preserveJoin A h (NativeAssoc.tagged S p) (NativeAssoc.tagged S (single S G)) e
    exact (congrArg (fun t => NativeAssoc.tagged S t ⋙ A.functor) (joinSingle S p G e).symm).trans
      ((congrArg (· ⋙ A.functor) j.symm).trans
        (r.trans ((joinEq M ih q).trans (StrictTelFold.read_grow S M L p G e).symm)))

include L s h in
/-- Both the objects and the maps of each length summand are recovered. -/
theorem unique : A = StrictTelFold.eval S M := by
  apply overExt
  fapply Functor.ext
  · rintro ⟨n,x⟩
    have z := uniquePath S A M L s h (⟨n,𝟭 _⟩ : NativeAssoc.Path S ((power S n).apex))
    exact Functor.congr_obj z x
  · rintro ⟨n,x⟩ ⟨_,y⟩ ⟨f⟩
    have z := uniquePath S A M L s h (⟨n,𝟭 _⟩ : NativeAssoc.Path S ((power S n).apex))
    exact Functor.congr_hom z f

theorem restriction_unit :
    (readOperations S (StrictTelFold.eval S M)).unit = M.unit := by
  apply overExt
  exact StrictTelFold.eval_zero S M

include L in
theorem restriction_tensor :
    (readOperations S (StrictTelFold.eval S M)).tensor = M.tensor := by
  apply overExt
  let K := Pair (power S 1) (power S 1)
  let p : NativeAssoc.Path S K.apex := single S (Strict.fst _ _)
  let q : NativeAssoc.Path S K.apex := single S (Strict.snd _ _)
  let j : NativeAssoc.dst S p = NativeAssoc.src S q := Strict.commute _ _
  have eq : (NativeAssoc.join S p q j).2 = (concatenate S 1 1).functor :=
    (blocks S 1 1).ext
      ((blocks S 1 1).first_assemble .. |>.trans (blocks S 1 1).join_first.symm)
      ((blocks S 1 1).rest_assemble .. |>.trans (blocks S 1 1).join_rest.symm)
  refine (congrArg (· ⋙ (StrictTelFold.comb S M 2).functor) eq.symm).trans ?_
  refine (StrictTelFold.read_join S M L p q j).trans ?_
  have C := Strict.uniq (power S 1).dest (power S 1).source (combine (Strict.fst _ _) (Strict.snd _ _) j) (𝟭 _) rfl rfl
  exact (congrArg (· ⋙ M.tensor.functor) C).trans (Functor.id_comp _)

end ContextualComposition.GrothendieckStep.StrictTelRecovery
