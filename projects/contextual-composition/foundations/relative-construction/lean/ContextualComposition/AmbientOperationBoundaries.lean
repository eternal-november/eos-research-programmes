module
public import ContextualComposition.AmbientBlockIteration
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientOperationBoundaries
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite NativeCleavage FibreValue TelescopeSquares NativeBlocks
open ContextadModification ContextadAmbientPayload AmbientRoundTrip AmbientBlockIteration ContextadRoutes ContextadLawTransport ContextadOuterCharts
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open ContextadNativeLaws
set_option maxHeartbeats 1600000
universe u v
section Generic
variable {B : Type u} [Category.{v} B] (Y Z W : Bᵒᵖ ⥤ Cat.{v,u})
variable {F : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)} {G : Total Z (𝟭 B) ⥤ Total W (𝟭 B)}
variable (h : F ⋙ proj Z = proj Y) (k : G ⋙ proj W = proj Z) (p : Pres F (proj Y) (proj Z)) (q : Pres G (proj Z) (proj W))
theorem descendComp (over : (F ⋙ G) ⋙ proj W = proj Y) :
    (decodedStrong Y Z F h p).vcomp (decodedStrong Z W G k q) =
    decodedStrong Y W (F ⋙ G) over (fun f t => q _ (p f t)) := by
  apply encodeInjective
  rw [strongComp,encodeDecode,encodeDecode,encodeDecode]
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {Y Z : PackedCuts.Psh.{u,max u v,u,v} B} (a : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor')
variable {i j : Nat} (r : Map S i j) (p : gradeCart r)
noncomputable def operationIso :
    ModIso ((blockStrong (S := S) a i).vcomp (nativeStrong Z r p))
      ((nativeStrong Y r p).vcomp (blockStrong (S := S) a j)) :=
  eqToIso (descendComp _ _ _ (blockOver S a i) (over Z r) (blockPres S a i) (globalPres Z r p) (rightOver a r)) ≪≫
    (weakOperationIso a r p).symm ≪≫
    eqToIso (descendComp _ _ _ (over Y r) (blockOver S a j) (globalPres Y r p) (blockPres S a j) (leftOver a r)).symm
section Transport
variable {C : Type u} [Category.{v} C] {G H : Cᵒᵖ ⥤ Cat.{v,u}}
variable (F J : ∀ A : C, G.obj (op A) ⥤ H.obj (op A)) (h : ∀ A, J A = F A)
variable (s : ∀ {A D : C} (f : A ⟶ D), (G.map f.op).toFunctor ⋙ F A ≅ F D ⋙ (H.map f.op).toFunctor)
noncomputable abbrev frame {A D : C} (f : A ⟶ D) :
    (G.map f.op).toFunctor ⋙ J A ≅ J D ⋙ (H.map f.op).toFunctor :=
  eqToIso (congrArg ((G.map f.op).toFunctor ⋙ ·) (h A)) ≪≫ s f ≪≫ eqToIso (congrArg (· ⋙ (H.map f.op).toFunctor) (h D).symm)
theorem frameEq (u c u' c') :
    ContextadStrong.assemble (G := G) (H := H) F s u c =
    ContextadStrong.assemble (G := G) (H := H) J (fun f => frame F J h s f) u' c' := by
  apply strongExt
  · funext A; exact congrArg Functor.toCatHom (h A.as.unop).symm
  · intro A D f x
    change HEq ((s f).hom.app x) ((frame F J h s f).hom.app x)
    simp only [frame,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app]
    exact ContextadUnitTotal.alignedHEq (AmbientDescentRecognition.trim _ _ _ ⟨_,rfl⟩ ⟨_,rfl⟩).symm
end Transport
theorem nativeMultiplication (m : ContextadTotal.Native S) (Q : PackedCuts.Psh.{u,max u v,u,v} B) :
    nativeStrong Q (tensor m) m.cart = ContextadStrong.multiplication m Q :=
  frameEq (G := PackedFree.pow S Q 2) (H := PackedFree.pow S Q 1) (ContextadTotal.binary m Q) (ContextadCoherence.actual m Q)
    (fun A => ContextadFinal.identify m _ Q A (ContextadSpecialize.agrees m A))
    (fun f => ContextadTotal.exterior m Q f) (ContextadCoherence.decodedUnit _ _ _ _ (ContextadTotal.totalCart m Q))
    (fun f g => ContextadCoherence.decodedComp _ _ _ _ (ContextadTotal.totalCart m Q) f g)
    (ContextadCoherence.unit m Q) (fun f g => ContextadCoherence.comp m Q f g)
noncomputable abbrev eta (S : P.Split) (d : ContextadUnit.Data P) (Q : PackedCuts.Psh.{u,max u v,u,v} B) :=
  nativeStrong Q (insert S d) (unitCart d)
noncomputable def unitIso (d : ContextadUnit.Data P) :
    ModIso (a.vcomp (eta S d Z)) ((eta S d Y).vcomp (layerStrong S a)) := by
  have h := operationIso a (insert S d) (unitCart d)
  rw [blockZero] at h
  exact h
noncomputable def tensorIso (m : ContextadTotal.Native S) :
    ModIso ((layerStrong S (layerStrong S a)).vcomp (ContextadStrong.multiplication m Z))
      ((ContextadStrong.multiplication m Y).vcomp (layerStrong S a)) := by
  have h := operationIso a (tensor m) m.cart
  rw [← blockTwo,nativeMultiplication,nativeMultiplication] at h
  exact h
end ContextualComposition.GrothendieckStep.AmbientOperationBoundaries
