module
public import ContextualComposition.AmbientModificationAction
public import ContextualComposition.AmbientVerticalDescent
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientBlockCells
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue NativeBlocks NativeCleavage
open ContextadAmbientPayload AmbientModificationAction ContextadWeakAction ContextadOuterCharts BoundaryPaste SpanApex
set_option backward.isDefEq.respectTransparency false
universe u v
section Generic
variable {B : Type u} [Category.{v} B] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} {K : Type*} [Category* K] (e : K ⥤ B)
variable {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} (t : StrongTrans.Modification a b)
noncomputable abbrev leaf (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') := actionLeaf e (totalStrong a) (strongOver a)
noncomputable def tail : atEndpoint a e ⋙ second (projectionData Z) e ⟶ atEndpoint b e ⋙ second (projectionData Z) e :=
  eqToHom (leaf e a) ≫ whiskerLeft (second (projectionData Y) e) (totalCell t) ≫ eqToHom (leaf e b).symm
theorem tailOver (x) : Pure ((pr Z).map ((tail e t).app x)) := by
  simp only [tail,NatTrans.comp_app,eqToHom_app,whiskerLeft_app,Functor.map_comp,eqToHom_map]
  exact pureComp ⟨_,rfl⟩ (pureComp (totalVertical t _) ⟨_,rfl⟩)
noncomputable abbrev head := (actionGrade e (totalStrong a) (strongOver a)).trans (actionGrade e (totalStrong b) (strongOver b)).symm
noncomputable def endpointCell : atEndpoint a e ⟶ atEndpoint b e :=
  ((whiskeringRight _ _ _).obj (intoPullback (projectionData Z) e)).preimage
    (mate Z e _ _ (head (a := a) (b := b) e) (tail e t) (tailOver e t))
theorem endpointOver (x) : Pure (gradeMap ((endpointCell e t).app x)) := by
  let J := (whiskeringRight (Total Y e) _ _).obj (intoPullback (projectionData Z) e)
  have z : J.map (endpointCell e t) = mate Z e _ _ (head (a := a) (b := b) e) (tail e t) (tailOver e t) := J.map_preimage _
  exact ⟨_,(congrArg (fun f => Limits.CategoricalPullback.Hom.fst f) (NatTrans.congr_app z x)).trans (eqToHom_app _ x)⟩
theorem endpointLeaf (x) :
    (second (projectionData Z) e).map ((endpointCell e t).app x) = (tail e t).app x := by
  let J := (whiskeringRight (Total Y e) _ _).obj (intoPullback (projectionData Z) e)
  have z : J.map (endpointCell e t) = mate Z e _ _ (head (a := a) (b := b) e) (tail e t) (tailOver e t) := J.map_preimage _
  exact congrArg (fun f => Limits.CategoricalPullback.Hom.snd f) (NatTrans.congr_app z x)
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {Y Z : PackedCuts.Psh.{u,max u v,u,v} B} {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'}
variable (t : StrongTrans.Modification a b)
noncomputable def blockCell (n : Nat) : blockTotal S a n ⟶ blockTotal S b n :=
  whiskerLeft (BlockEvaluation.global S Y n).strictInv (whiskerRight (endpointCell (power S n).dest t) (BlockEvaluation.global S Z n))
theorem blockVertical (n : Nat) (x) : Pure ((proj (PackedFree.pow S Z n)).map ((blockCell S t n).app x)) := by
  let f := (endpointCell (power S n).dest t).app ((BlockEvaluation.global S Y n).strictInv.obj x)
  change Pure ((BlockEvaluation.global S Z n ⋙ proj (PackedFree.pow S Z n)).map f)
  rw [BlockEvaluation.globalOver]
  exact pureMap (power S n).source (endpointOver _ t _)
noncomputable def blockMod (n : Nat) : StrongTrans.Modification (blockStrong (S := S) a n) (blockStrong (S := S) b n) :=
  AmbientVerticalDescent.descend _ _ (blockOver S a n) (blockOver S b n) (blockCell S t n) (blockVertical S t n) (blockPres S a n) (blockPres S b n)
noncomputable def layerMod : StrongTrans.Modification (layerStrong S a) (layerStrong S b) := blockMod S t 1
end ContextualComposition.GrothendieckStep.AmbientBlockCells
