module
public import ContextualComposition.AmbientBicategory
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientMateCalculus
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares NativeCleavage
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientDescentRecognition ContextadWeakAction ContextadWeakWeight ContextadOuterCharts
open SpanApex BoundaryPaste
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {B K L : Type u} [Category.{v} B] [Category.{v} K] [Category.{v} L]
variable {Y Z W : Bᵒᵖ ⥤ Cat.{v,u}} (e : K ⥤ B) (d : L ⥤ B) (r : K ⥤ L) (δ : r ⋙ d ⟶ e)
variable {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} (t : StrongTrans.Modification a b)
theorem endpointLeafAlign (x) :
    Aligned ((leafAt Z e).map ((endpointCell e t).app x)) ((totalCell t).app ((leafAt Y e).obj x)) := by
  rw [show (leafAt Z e).map _ = _ from endpointLeaf e t x]
  exact trim _ _ _ ⟨_,eqToHom_app _ _⟩ ⟨_,eqToHom_app _ _⟩
variable (a)
noncomputable abbrev q := (weakSquare e d r δ a).hom
theorem mateLeaf (x) :
    (leafAt Z d).map ((q e d r δ a).app x) = (payloadMate e d r δ a).hom.app x := by
  let J := (whiskeringRight (Total Y e) _ _).obj (intoPullback (projectionData Z) d)
  have z : J.map (q e d r δ a) = mate Z d _ _ (sameGrade e d r δ a) (payloadMate e d r δ a).hom (mateBase e d r δ a) := J.map_preimage _
  exact congrArg (fun f => Limits.CategoricalPullback.Hom.snd f) (NatTrans.congr_app z x)
theorem factor (x) :
    Aligned ((leafAt Z d).map ((q e d r δ a).app x) ≫ (tip Z e d r δ).app ((atEndpoint a e).obj x))
      ((totalStrong a).map ((tip Y e d r δ).app x)) := by
  rw [mateLeaf]
  apply ((Aligned.refl _).comp (rightAligned e d r δ a x).symm).trans
  exact (NativeCube.ofEq (factorFac (proj Z) _ _ (sameBase e d r δ a) (coneOver e d r δ a) (rCart e d r δ a) x)).trans (leftAligned e d r δ a x)
theorem foldEqual {x y : Total Z d} {f g : x ⟶ y} (h : gradeMap f = gradeMap g)
    (k : (leafAt Z d).map f = (leafAt Z d).map g) : f = g := by
  apply (intoPullback (projectionData Z) d).map_injective
  exact Limits.CategoricalPullback.hom_ext h k
theorem cancelTip {x : Total Z d} (y : Total Z e) (f g : x ⟶ (restrict Z e d r δ).obj y)
    (h : Pure (gradeMap f)) (k : Pure (gradeMap g))
    (l : Aligned ((leafAt Z d).map f ≫ (tip Z e d r δ).app y) ((leafAt Z d).map g ≫ (tip Z e d r δ).app y)) :
    f = g := by
  apply foldEqual d (pureEq h k)
  apply cancel (proj Z) _ (tipCart Z e d r δ y)
  · exact congrArg d.map (pureEq h k)
  · exact l.eq
variable {a}
theorem modificationSquare (x : Total Y e) :
    (q e d r δ a).app x ≫ (restrict Z e d r δ).map ((endpointCell e t).app x) =
    (endpointCell d t).app ((restrict Y e d r δ).obj x) ≫ (q e d r δ b).app x := by
  let R := restrict Z e d r δ
  let J := leafAt Z d
  let H := leafAt Z e
  let v := (endpointCell e t).app x
  let k := (q e d r δ a).app x
  let j := (q e d r δ b).app x
  let u := (endpointCell d t).app ((restrict Y e d r δ).obj x)
  apply cancelTip e d r δ ((atEndpoint b e).obj x)
  · exact pureComp (weakGrade e d r δ a x) (pureMap r (endpointOver e t x))
  · exact pureComp (endpointOver d t _) (weakGrade e d r δ b x)
  · change Aligned (J.map (k ≫ R.map v) ≫ _) (J.map (u ≫ j) ≫ _)
    have nat : J.map (R.map v) ≫ (tip Z e d r δ).app ((atEndpoint b e).obj x) =
        (tip Z e d r δ).app ((atEndpoint a e).obj x) ≫ H.map v := (tip Z e d r δ).naturality v
    rw [Functor.map_comp,Functor.map_comp,Category.assoc,Category.assoc,nat,← Category.assoc]
    apply ((factor e d r δ a x).comp (endpointLeafAlign e t x)).trans
    apply (NativeCube.ofEq ((totalCell t).naturality ((tip Y e d r δ).app x))).trans
    exact ((endpointLeafAlign d t _).comp (factor e d r δ b x)).symm
theorem pureOfAligned {C : Type*} [Category* C] {x y z w : C} {f : x ⟶ y} {g : z ⟶ w} (h : Aligned f g) (p : Pure g) : Pure f := by
  obtain ⟨rfl,rfl,h⟩ := h; simp at h; exact h ▸ p
variable (a) (c : StrongTrans Z.toPseudofunctor' W.toPseudofunctor')
noncomputable def doubled : lRoute e d r δ (a.vcomp c) ⟶ rRoute e d r δ (a.vcomp c) :=
  eqToHom (congrArg (restrict Y e d r δ ⋙ ·) (atEndpointComp a c d)) ≫
    (whiskerRight (q e d r δ a) (atEndpoint c d) ≫ whiskerLeft (atEndpoint a e) (q e d r δ c)) ≫
    eqToHom (congrArg (· ⋙ restrict W e d r δ) (atEndpointComp a c e).symm)
theorem doubledAt (x) : Aligned ((doubled e d r δ a c).app x)
    ((atEndpoint c d).map ((q e d r δ a).app x) ≫ (q e d r δ c).app ((atEndpoint a e).obj x)) := by
  exact trim _ _ _ ⟨_,eqToHom_app _ _⟩ ⟨_,eqToHom_app _ _⟩
theorem compSquare : q e d r δ (a.vcomp c) = doubled e d r δ a c := by
  apply NatTrans.ext; funext x
  let u := (q e d r δ a).app x
  let y := (atEndpoint a e).obj x
  let v := (q e d r δ c).app y
  let U := atEndpoint c d
  let F := totalStrong c
  let J := leafAt W d
  let l := tip W e d r δ
  let b := (doubled e d r δ a c).app x
  have ht := doubledAt e d r δ a c x
  have gU : Aligned (gradeMap (U.map u)) (gradeMap u) := NativeCube.functorAlign (actionGrade d (totalStrong c) (strongOver c)) u
  apply cancelTip e d r δ ((atEndpoint (a.vcomp c) e).obj x) _ _ (weakGrade e d r δ _ _)
  · exact pureOfAligned (ht.map gradeProjection) (pureComp (pureOfAligned gU (weakGrade e d r δ a x)) (weakGrade e d r δ c y))
  · apply (factor e d r δ (a.vcomp c) x).trans; apply Aligned.symm
    have hy := Functor.congr_obj (atEndpointComp a c e) x
    apply ((ht.map J).comp (ContextadPayloadModification.appChange l hy)).trans
    change Aligned (J.map (U.map u ≫ v) ≫ l.app ((atEndpoint c e).obj y)) _
    rw [Functor.map_comp,Category.assoc]
    apply ((NativeCube.functorAlign (actionLeaf d (totalStrong c) (strongOver c)) u).comp (factor e d r δ c y)).trans
    apply (NativeCube.ofEq (F.map_comp _ _).symm).trans
    exact (((factor e d r δ a x).map F).trans (NativeCube.functorAlign (strongComp a c).symm ((tip Y e d r δ).app x)))
theorem endpointId (G : Bᵒᵖ ⥤ Cat.{v,u}) {T : Type u} [Category.{v} T] (f : T ⥤ B) :
    atEndpoint (𝟙 G.toPseudofunctor') f = 𝟭 _ :=
  (ContextadUnitTotal.congrAction f _ rfl (strongId (Y := G))).trans (actionIdentity f)
theorem idRoutes (G : Bᵒᵖ ⥤ Cat.{v,u}) : lRoute e d r δ (𝟙 G.toPseudofunctor') = rRoute e d r δ (𝟙 G.toPseudofunctor') := by
  unfold lRoute rRoute; rw [endpointId,endpointId]; rfl
theorem idSquare (G : Bᵒᵖ ⥤ Cat.{v,u}) : q e d r δ (𝟙 G.toPseudofunctor') = eqToHom (idRoutes e d r δ G) := by
  apply NatTrans.ext; funext x
  let b := (atEndpoint (𝟙 G.toPseudofunctor') e).obj x
  let f := (eqToHom (idRoutes e d r δ G)).app x
  let M := leafAt G d
  have hv : Pure f := ⟨_,eqToHom_app _ x⟩
  apply cancelTip e d r δ b _ _ (weakGrade e d r δ _ _) (pureMap gradeProjection hv)
  apply (factor e d r δ (𝟙 G.toPseudofunctor') x).trans
  apply (NativeCube.functorAlign (strongId (Y := G)) ((tip G e d r δ).app x)).trans
  apply Aligned.symm
  have h : Aligned (M.map f ≫ (tip G e d r δ).app b) ((tip G e d r δ).app b) := by
    obtain ⟨e₀,w⟩ := pureMap M hv
    rw [w]
    exact ⟨e₀,rfl,by simp⟩
  exact h.trans (ContextadPayloadModification.appChange _ (Functor.congr_obj (endpointId G e) x))
end ContextualComposition.GrothendieckStep.AmbientMateCalculus
