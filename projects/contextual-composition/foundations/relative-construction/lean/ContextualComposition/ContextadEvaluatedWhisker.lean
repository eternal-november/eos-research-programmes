module
public import ContextualComposition.ContextadHorizontalModification
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadEvaluatedWhisker
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadLawTransport ContextadCellWhisker ContextadPayloadModification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) {i j k l : Nat} {f g : Map S j k} (a : Cell f g)
theorem rawBefore (p : Map S i j) (x) : Aligned ((rawCell Y (before a p)).hom.app x) ((rawCell Y a).hom.app ((raw Y p).obj x)) :=
  ⟨Functor.congr_obj (rawCompose Y p f) x,Functor.congr_obj (rawCompose Y p g) x,by
    simpa only [NatTrans.comp_app,eqToHom_app,whiskerLeft_app] using NatTrans.congr_app (beforeSquare a Y p) x⟩
theorem rawAfter (q : Map S k l) (x) : Aligned ((rawCell Y (after a q)).hom.app x) ((raw Y q).map ((rawCell Y a).hom.app x)) :=
  ⟨Functor.congr_obj (rawCompose Y f q) x,Functor.congr_obj (rawCompose Y g q) x,by
    simpa only [NatTrans.comp_app,eqToHom_app,whiskerRight_app] using NatTrans.congr_app (afterSquare a Y q) x⟩
theorem totalBefore (p : Map S i j) (x) : Aligned ((globalCell Y (before a p)).hom.app x) ((globalCell Y a).hom.app ((global Y p).obj x)) := by
  let E := BlockEvaluation.global S Y j
  let D := BlockEvaluation.global S Y k
  let w := (BlockEvaluation.global S Y i).strictInv.obj x
  let z := (raw Y p).obj w
  have h : z = (E ⋙ E.strictInv).obj z := Functor.congr_obj E.asIsomorphism.unit_eq z
  exact ((rawBefore Y a p w).trans (appChange (rawCell Y a).hom h)).map D
theorem totalAfter (q : Map S k l) (x) : Aligned ((globalCell Y (after a q)).hom.app x) ((global Y q).map ((globalCell Y a).hom.app x)) := by
  let E := BlockEvaluation.global S Y k
  let D := BlockEvaluation.global S Y l
  let w := (BlockEvaluation.global S Y j).strictInv.obj x
  let b := (rawCell Y a).hom.app w
  have h : raw Y q = (E ⋙ E.strictInv) ⋙ raw Y q :=
    (Functor.id_comp _).symm.trans (congrArg (· ⋙ raw Y q) E.asIsomorphism.unit_eq)
  exact ((rawAfter Y a q w).trans (NativeCube.functorAlign h b)).map D
theorem reflectIncl (n : Nat) (A : B) {x y x' y' : (PackedFree.pow S Y n).obj (op A)} {f : x ⟶ y} {g : x' ⟶ y'}
    (h : Aligned ((incl (PackedFree.pow S Y n) A).map f) ((incl (PackedFree.pow S Y n) A).map g)) : Aligned f g := by
  let H := PackedFree.pow S Y n
  let I := incl H A
  let _ : I.Faithful := (inferInstance : (embed H A ⋙ Fiber.fiberInclusion).Faithful)
  apply reflectAlign I _ _ _ h
  intro a b e
  exact congrArg (value H A).obj (show (embed H A).obj a = (embed H A).obj b from Subtype.ext e)
theorem evalBefore (p : Map S i j) (A : B) (x) : Aligned ((evalCell Y (before a p) A).hom.app x)
    ((evalCell Y a A).hom.app ((evaluate Y p A).obj x)) := by
  apply reflectIncl Y k A
  exact (includeCell (before a p) Y A x).trans ((totalBefore Y a p _).trans
    ((appChange (globalCell Y a).hom (Functor.congr_obj (evalIncl Y p A).symm x)).trans (includeCell a Y A _).symm))
theorem evalAfter (q : Map S k l) (A : B) (x) : Aligned ((evalCell Y (after a q) A).hom.app x)
    ((evaluate Y q A).map ((evalCell Y a A).hom.app x)) := by
  apply reflectIncl Y l A
  exact (includeCell (after a q) Y A x).trans ((totalAfter Y a q _).trans
    (((includeCell a Y A x).symm.map (global Y q)).trans (NativeCube.functorAlign (evalIncl Y q A).symm _)))
end ContextualComposition.GrothendieckStep.ContextadEvaluatedWhisker
