module
public import ContextualComposition.StrictTelFold
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictTelOperations
open CategoryTheory SpanApex NativeBlocks
open NativeBlocks.Nested (Over whole word outer collapse flatten)
open StrictSpanAlgebra
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B] {P : Endpoints.{b,max b w,b,max b w} B} (S : P.Split)

noncomputable def ops : Ops (whole S) where
  unit := ⟨incl S 0,rfl,rfl⟩
  tensor := ⟨binary S,binary_source S,binary_dest S⟩

theorem strict : Laws (ops S) where
  left F := NativeAssoc.Whole.mul_left S F
  right F := NativeAssoc.Whole.mul_right S F
  assoc F G H e d := NativeAssoc.Whole.mul_assoc S F G H e d

def generator : Over (power S 1) (whole S) := ⟨incl S 1,rfl,rfl⟩

theorem zero_ne_generator (A : B) (x : (power S 1).apex) :
    (incl S 0).obj A ≠ (generator S).functor.obj x :=
  fun h => Nat.zero_ne_one (congrArg Sigma.fst h)

section Hom
variable {U V : Span (B := B)} {M : Ops U} {N : Ops V} (F : Over U V)
structure Multiplicative : Prop where
  unit : M.unit.functor ⋙ F.functor = N.unit.functor
  tensor : M.tensor.functor ⋙ F.functor =
    (both F F).functor ⋙ N.tensor.functor

variable {X : Type*} [Category* X] (L : Multiplicative F (M := M) (N := N))
include L in
theorem preserveOne (A : X ⥤ B) : one M A ⋙ F.functor = one N A :=
  congrArg (A ⋙ ·) L.unit
include L in
theorem preserveJoin (p q : X ⥤ U.apex) (h : p ⋙ U.dest = q ⋙ U.source) :
    join M p q h ⋙ F.functor =
      join N (p ⋙ F.functor) (q ⋙ F.functor)
        ((congrArg (p ⋙ ·) F.dest).trans (h.trans (congrArg (q ⋙ ·) F.source.symm))) :=
  (congrArg (combine p q h ⋙ ·) L.tensor).trans
    (congrArg (· ⋙ N.tensor.functor) (combine_both F F p q h))

theorem preserveJoin_iff :
    (∀ (p q : (Pair U U).apex ⥤ U.apex) (h : p ⋙ U.dest = q ⋙ U.source),
      join M p q h ⋙ F.functor =
        join N (p ⋙ F.functor) (q ⋙ F.functor)
          ((congrArg (p ⋙ ·) F.dest).trans (h.trans (congrArg (q ⋙ ·) F.source.symm)))) ↔
      (M.tensor.functor ⋙ F.functor = (both F F).functor ⋙ N.tensor.functor) := by
  constructor
  · intro h
    have e := h (Strict.fst _ _) (Strict.snd _ _) (Strict.commute _ _)
    exact (congrArg (fun z => z ⋙ M.tensor.functor ⋙ F.functor)
      (Strict.uniq U.dest U.source (𝟭 _) (combine (Strict.fst _ _) (Strict.snd _ _) (Strict.commute _ _)) rfl rfl)).trans e
  · intro t p q h
    exact (congrArg (combine p q h ⋙ ·) t).trans (congrArg (· ⋙ N.tensor.functor) (combine_both F F p q h))
end Hom

theorem foldTensorAt (M : Ops (power S 1)) (D : Laws M) (m n : Nat) :
    tagPair S (m,n) ⋙ binary S ⋙ (StrictTelFold.eval S M).functor =
      tagPair S (m,n) ⋙ (both (StrictTelFold.eval S M) (StrictTelFold.eval S M)).functor ⋙ M.tensor.functor := by
  let p : NativeAssoc.Path S (part S (m,n)) := ⟨m,Strict.fst _ _⟩
  let q : NativeAssoc.Path S (part S (m,n)) := ⟨n,Strict.snd _ _⟩
  let h : NativeAssoc.dst S p = NativeAssoc.src S q := Strict.commute _ _
  let E := StrictTelFold.eval S M
  let F := Strict.fst (power S m).dest (power S n).source ⋙ incl S m
  let G := Strict.snd (power S m).dest (power S n).source ⋙ incl S n
  have k : F ⋙ rightLeg S = G ⋙ leftLeg S := Strict.commute (power S m).dest (power S n).source
  change combine (U := whole S) (V := whole S) F G k ⋙ binary S ⋙ E.functor =
         combine (U := whole S) (V := whole S) F G k ⋙ (both E E).functor ⋙ M.tensor.functor
  exact (congrArg (· ⋙ E.functor) (NativeAssoc.tag_join S p q h)).trans <|
    (StrictTelFold.read_join S M D p q h).trans <|
      (congrArg (· ⋙ M.tensor.functor) (combine_both E E F G k)).symm

theorem foldMultiplicative (M : Ops (power S 1)) (D : Laws M) :
    Multiplicative (StrictTelFold.eval S M) (M := ops S) (N := M) where
  unit := StrictTelFold.eval_zero S M
  tensor := by
    let J := Sigma.desc (fun i : Nat × Nat => tagPair S i)
    have eq : J ⋙ binary S ⋙ (StrictTelFold.eval S M).functor =
        J ⋙ (both (StrictTelFold.eval S M) (StrictTelFold.eval S M)).functor ⋙ M.tensor.functor := by
      fapply Functor.ext
      · rintro ⟨⟨m,n⟩,x⟩; exact Functor.congr_obj (foldTensorAt S M D m n) x
      · rintro ⟨⟨m,n⟩,x⟩ ⟨_,y⟩ ⟨f⟩; exact Functor.congr_hom (foldTensorAt S M D m n) f
    exact ((congrArg (· ⋙ binary S ⋙ (StrictTelFold.eval S M).functor) (split_gather S).symm).trans
      ((congrArg (splitPairs S ⋙ ·) eq).trans
      (congrArg (· ⋙ (both (StrictTelFold.eval S M) (StrictTelFold.eval S M)).functor ⋙ M.tensor.functor)
        (split_gather S))))

end ContextualComposition.GrothendieckStep.StrictTelOperations
