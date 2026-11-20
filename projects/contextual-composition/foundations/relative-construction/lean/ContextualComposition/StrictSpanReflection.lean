module
public import ContextualComposition.StrictTelOperations
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictSpanReflection
open CategoryTheory NativeBlocks
open NativeBlocks.Nested (Over)
open StrictSpanAlgebra StrictTelOperations
universe b w
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
variable {B : Type b} [Category.{max b w} B] {U V : Span (B := B)} {M : Ops U} {N : Ops V}
variable (F : Over U V) (J : Over V U) (E : J.functor ⋙ F.functor = 𝟭 _)
variable {X : Type b} [Category.{max b w} X]

abbrev lift (G : X ⥤ V.apex) := G ⋙ J.functor
theorem liftSrc (G : X ⥤ V.apex) : lift J G ⋙ U.source = G ⋙ V.source := congrArg (G ⋙ ·) J.source
theorem liftDst (G : X ⥤ V.apex) : lift J G ⋙ U.dest = G ⋙ V.dest := congrArg (G ⋙ ·) J.dest
include E in
theorem liftRet (G : X ⥤ V.apex) : lift J G ⋙ F.functor = G :=
  (congrArg (G ⋙ ·) E).trans (Functor.comp_id _)

variable (h : Multiplicative F (M := M) (N := N)) (k : Laws M)
include F J E h k
theorem recoverLeft (G : X ⥤ V.apex) :
    join N (one N (G ⋙ V.source)) G (one_dst N _) = G := by
  let t := lift J G
  let u := one M (t ⋙ U.source)
  have e₁ : u ⋙ F.functor = one N (G ⋙ V.source) :=
    (preserveOne F h _).trans (congrArg (one N) (liftSrc J G))
  have e₂ := liftRet F J E G
  exact (joinEq N e₁.symm e₂.symm).trans ((preserveJoin F h u t (one_dst M _)).symm.trans
    ((congrArg (· ⋙ F.functor) (k.left t)).trans e₂))

theorem recoverRight (G : X ⥤ V.apex) :
    join N G (one N (G ⋙ V.dest)) (one_src N _).symm = G := by
  let t := lift J G
  let u := one M (t ⋙ U.dest)
  have e₁ : u ⋙ F.functor = one N (G ⋙ V.dest) :=
    (preserveOne F h _).trans (congrArg (one N) (liftDst J G))
  have e₂ := liftRet F J E G
  exact (joinEq N e₂.symm e₁.symm).trans ((preserveJoin F h t u (one_src M _).symm).symm.trans
    ((congrArg (· ⋙ F.functor) (k.right t)).trans e₂))

theorem recoverAssoc (p q r : X ⥤ V.apex) (e : p ⋙ V.dest = q ⋙ V.source)
    (d : q ⋙ V.dest = r ⋙ V.source) :
    join N (join N p q e) r ((join_dst N p q e).trans d) =
      join N p (join N q r d) (e.trans (join_src N q r d).symm) := by
  let p' := lift J p; let q' := lift J q; let r' := lift J r
  let e' : p' ⋙ U.dest = q' ⋙ U.source := (liftDst J p).trans (e.trans (liftSrc J q).symm)
  let d' : q' ⋙ U.dest = r' ⋙ U.source := (liftDst J q).trans (d.trans (liftSrc J r).symm)
  let pq := join M p' q' e'
  let qr := join M q' r' d'
  have ep := liftRet F J E p
  have eq := liftRet F J E q
  have er := liftRet F J E r
  have i : pq ⋙ F.functor = join N p q e := (preserveJoin F h p' q' e').trans (joinEq N ep eq)
  have j : qr ⋙ F.functor = join N q r d := (preserveJoin F h q' r' d').trans (joinEq N eq er)
  have l := preserveJoin F h pq r' ((join_dst M p' q' e').trans d')
  have s := preserveJoin F h p' qr (e'.trans (join_src M q' r' d').symm)
  exact (l.trans (joinEq N i er)).symm.trans
    ((congrArg (· ⋙ F.functor) (k.assoc p' q' r' e' d')).trans (s.trans (joinEq N ep j)))

/-- Reflection uses a strict span section, not descent through an
unexamined isomorphism or a selected section on objects alone. -/
theorem reflect : Laws N where
  left := recoverLeft F J E h k
  right := recoverRight F J E h k
  assoc := recoverAssoc F J E h k

end ContextualComposition.GrothendieckStep.StrictSpanReflection
