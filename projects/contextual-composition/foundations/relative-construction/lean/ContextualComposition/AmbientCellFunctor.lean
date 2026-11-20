module
public import ContextualComposition.AmbientBlockIteration
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCellFunctor
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientVerticalDescent SpanApex BoundaryPaste ContextadWeakAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{v} B] {Y Z : Bᵒᵖ ⥤ Cat.{v,u}}
variable {a b c : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} (t : StrongTrans.Modification a b) (s : StrongTrans.Modification b c)
theorem totalApp (x : Total Y (𝟭 B)) :
    (totalCell t).app x = (incl Z (grade _ _ x)).map ((t.app ⟨op (grade _ _ x)⟩).toNatTrans.app (payload _ _ x)) := by
  apply (homEquiv _ _).injective; refine Sigma.ext rfl ?_
  apply HEq.trans _ (embed_payload Z _).symm
  change HEq (_ ≫ (Z.toPseudofunctor'.mapId _).inv.toNatTrans.app _) _
  simp only [Functor.toPseudofunctor'_mapId,eqToIso.inv,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app]
  exact ContextadUnitTotal.alignedHEq (Aligned.trailing _ _)
theorem totalId (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') : totalCell (StrongTrans.Modification.id a) = 𝟙 (totalStrong a) := by
  ext x : 2
  rw [totalApp]
  exact (incl Z _).map_id _
theorem totalComp : totalCell (t.vcomp s) = totalCell t ≫ totalCell s := by
  ext x : 2
  simp only [NatTrans.comp_app,totalApp]
  exact (incl Z _).map_comp _ _
variable {K : Type*} [Category* K] (e : K ⥤ B)
theorem endpointId (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor') :
    endpointCell e (StrongTrans.Modification.id a) = 𝟙 (atEndpoint a e) := by
  let J := (whiskeringRight (Total Y e) _ _).obj (intoPullback (projectionData Z) e)
  apply J.map_injective
  rw [show J.map (endpointCell e _) = _ from J.map_preimage _,J.map_id]
  apply NatTrans.ext; funext x
  apply Limits.CategoricalPullback.hom_ext
  · simp [ContextadOuterCharts.mate]; rfl
  · change (AmbientBlockCells.tail e (StrongTrans.Modification.id a)).app x = 𝟙 _
    simp [AmbientBlockCells.tail,totalId]
theorem endpointComp : endpointCell e (t.vcomp s) = endpointCell e t ≫ endpointCell e s := by
  let J := (whiskeringRight (Total Y e) _ _).obj (intoPullback (projectionData Z) e)
  apply J.map_injective
  rw [J.map_comp,show J.map (endpointCell e _) = _ from J.map_preimage _,
    show J.map (endpointCell e t) = _ from J.map_preimage _,show J.map (endpointCell e s) = _ from J.map_preimage _]
  apply NatTrans.ext; funext x
  apply Limits.CategoricalPullback.hom_ext
  · simp [ContextadOuterCharts.mate,eqToHom_app]
  · change (AmbientBlockCells.tail e (t.vcomp s)).app x = (AmbientBlockCells.tail e t).app x ≫ (AmbientBlockCells.tail e s).app x
    simp [AmbientBlockCells.tail,totalComp,Category.assoc,eqToHom_app]

section Vertical
variable {C D T : Type*} [Category* C] [Category* D] [Category* T] {p : C ⥤ T} {q : D ⥤ T}
variable {F G H : C ⥤ D} (h : F ⋙ q = p) (k : G ⋙ q = p) (l : H ⋙ q = p)
variable (i : F ⟶ G) (j : G ⟶ H) (v : ∀ x, Pure (q.map (i.app x))) (w : ∀ x, Pure (q.map (j.app x)))
theorem fibreId (A : T) (u : ∀ x, Pure (q.map ((𝟙 F : F ⟶ F).app x))) :
    fibre h h (𝟙 F) u A = 𝟙 _ := by
  apply NatTrans.ext; funext x; apply Subtype.ext
  simp [fibre]; rfl
theorem fibreComp (A : T) (u : ∀ x, Pure (q.map ((i ≫ j).app x))) :
    fibre h l (i ≫ j) u A = fibre h k i v A ≫ fibre k l j w A := by
  apply NatTrans.ext; funext x; apply Subtype.ext
  change _ = ((fibre h k i v A).app x).val ≫ ((fibre k l j w A).app x).val
  simp [fibre,eqToHom_app,Category.assoc]
end Vertical
section Packed
open NativeBlocks
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {U V : PackedCuts.Psh.{u,max u v,u,v} B} {a b c : StrongTrans U.toPseudofunctor' V.toPseudofunctor'}
theorem blockCellId (a : StrongTrans U.toPseudofunctor' V.toPseudofunctor') (n : Nat) :
    blockCell S (StrongTrans.Modification.id a) n = 𝟙 _ := by
  unfold blockCell; rw [endpointId]; simp; rfl
theorem blockCellComp (t : StrongTrans.Modification a b) (s : StrongTrans.Modification b c) (n : Nat) :
    blockCell S (t.vcomp s) n = blockCell S t n ≫ blockCell S s n := by
  unfold blockCell; rw [endpointComp]; simp
theorem blockModId (a : StrongTrans U.toPseudofunctor' V.toPseudofunctor') (n : Nat) :
    blockMod S (StrongTrans.Modification.id a) n = StrongTrans.Modification.id (blockStrong (S := S) a n) := by
  apply StrongTrans.Modification.ext; funext A
  apply Cat.Hom₂.ext; ext x : 2
  change (value _ _).map ((fibre _ _ _ _ _).app _) = 𝟙 _
  simp only [blockCellId,fibreId,NatTrans.id_app,Functor.map_id]
theorem blockModComp (t : StrongTrans.Modification a b) (s : StrongTrans.Modification b c) (n : Nat) :
    blockMod S (t.vcomp s) n = (blockMod S t n).vcomp (blockMod S s n) := by
  apply StrongTrans.Modification.ext; funext A
  apply Cat.Hom₂.ext; ext x : 2
  change (value _ _).map ((fibre _ _ _ _ _).app _) = (value _ _).map _ ≫ (value _ _).map _
  simp only [blockCellComp,fibreComp (blockOver S a n) (blockOver S b n) (blockOver S c n) _ _ (blockVertical S t n) (blockVertical S s n),NatTrans.comp_app,Functor.map_comp]
noncomputable def homFunctor (U V : PackedCuts.Psh.{u,max u v,u,v} B) (n : Nat) :
    (U.toPseudofunctor' ⟶ V.toPseudofunctor') ⥤ ((PackedFree.pow S U n).toPseudofunctor' ⟶ (PackedFree.pow S V n).toPseudofunctor') where
  obj a := blockStrong (S := S) a n
  map t := ⟨blockMod S t.as n⟩
  map_id a := StrongTrans.Hom.ext (blockModId S a n)
  map_comp t s := StrongTrans.Hom.ext (blockModComp S t.as s.as n)
end Packed
end ContextualComposition.GrothendieckStep.AmbientCellFunctor
