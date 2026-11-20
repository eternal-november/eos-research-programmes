module
public import ContextualComposition.AmbientPseudonaturality
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientNativeModification
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells ContextadWeakAction ContextadWeakWeight
open AmbientBicategory AmbientCoordinates ContextadLawTransport ContextadModification NativeBlocks WordTrace CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
theorem unbend {C : Type*} [Category C] {a b c d : C} (u : a ≅ b) (v : c ≅ d) (l : a ⟶ c) (r : b ⟶ d)
    (h : u.inv ≫ l = r ≫ v.inv) : l ≫ v.hom = u.hom ≫ r := by
  apply (cancel_epi u.inv).mp
  rw [← Category.assoc,h,Category.assoc,Iso.inv_hom_id,Category.comp_id,Iso.inv_hom_id_assoc]
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X Y : Obj.{u,v} B} {i j : Nat} {r s : ContextadRoutes.Map S i j} (c : Cell r s) (p : gradeCart r) (q : gradeCart s)
noncomputable def cmp (X : Obj.{u,v} B) : oper S r p X ≅ oper S s q X :=
  Bicategory.InducedBicategory.isoMk (invertibleMod _ _ (global X r) (global X s) (over X r) (over X s) (globalCell X c) (globalVertical X c) (globalPres X r p) (globalPres X s q))
theorem cmpAt (x) : Aligned (atRaw S (cmp c p q X).hom x) ((rawCell X c).hom.app x) :=
  ((AmbientComparisonRead.isoModAt _ _ _ _ (globalCell X c) (globalVertical X c) (globalPres X r p) (globalPres X s q) ((chart S X i).obj x)).map (chart S X j).strictInv).trans
    (AmbientComparisonRead.chartConj _ _ _ x)
abbrev tip (X : Obj.{u,v} B) (r : ContextadRoutes.Map S i j) := ContextadWeakWeight.tip (underlying X) (power S i).dest (power S j).dest r.grade r.leg
abbrev leaf (X : Obj.{u,v} B) (n : Nat) := leafAt (underlying X) (power S n).dest
theorem tipFactor (X : Obj.{u,v} B) (x) :
    (leaf (S := S) X j).map ((rawCell X c).hom.app x) ≫ (tip X s).app x = (tip X r).app x := by
  apply WeightedCells.pureArrowEq _ (𝟭 B)
  · rw [grade_comp]
    change (power S j).dest.map (gradeMap ((rawCell X c).hom.app x)) ≫ s.leg.app _ = r.leg.app _
    rw [show gradeMap ((rawCell X c).hom.app x) = _ from WeightedCells.weightGrade _ _ _ _ c.endpoint x]
    exact NatTrans.congr_app c.endpoint _
  · exact WeightedCells.totalPureComp _ _ (WeightedCells.weightPayloadPure _ _ _ _ c.endpoint x) (pureId _)
  · exact pureId _
variable (f : X ⟶ Y)
theorem rawSquare (x) :
    (AmbientComparisonRead.q S r f).app x ≫ (rawCell Y c).hom.app ((atEndpoint f.hom (power S i).dest).obj x) =
    (atEndpoint f.hom (power S j).dest).map ((rawCell X c).hom.app x) ≫ (AmbientComparisonRead.q S s f).app x := by
  let U := atEndpoint f.hom (power S j).dest
  let V := totalStrong f.hom
  let y := (atEndpoint f.hom (power S i).dest).obj x
  let J := leaf (S := S) Y j
  let q₁ := (AmbientComparisonRead.q S r f).app x
  let q₂ := (AmbientComparisonRead.q S s f).app x
  let a := (rawCell X c).hom.app x
  let b := (rawCell Y c).hom.app y
  have gb : Aligned (gradeMap b) (c.grade.hom.app (grade (underlying X) _ x)) :=
    (NativeCube.ofEq (WeightedCells.weightGrade _ _ _ _ c.endpoint y)).trans
      (ContextadPayloadModification.appChange c.grade.hom (Functor.congr_obj (actionGrade _ (totalStrong f.hom) (strongOver f.hom)) x))
  have ga : Aligned (gradeMap (U.map a)) (c.grade.hom.app (grade (underlying X) _ x)) :=
    (NativeCube.functorAlign (actionGrade _ (totalStrong f.hom) (strongOver f.hom)) a).trans (NativeCube.ofEq (WeightedCells.weightGrade _ _ _ _ c.endpoint x))
  have hg : gradeMap (q₁ ≫ b) = gradeMap (U.map a ≫ q₂) := by
    have h₁ := weakGrade _ _ r.grade r.leg f.hom x
    have h₂ := weakGrade _ _ s.grade s.leg f.hom x
    obtain ⟨u,z⟩ := h₁; obtain ⟨v,w⟩ := h₂
    change gradeMap q₁ = _ at z; change gradeMap q₂ = _ at w
    rw [grade_comp,grade_comp,z,w]
    have castL : Aligned (eqToHom u ≫ gradeMap b) (gradeMap b) := ⟨u,rfl,by simp⟩
    exact (castL.trans (gb.trans (ga.symm.trans (Aligned.trailing _ v).symm))).eq
  apply AmbientMateCalculus.foldEqual (power S j).dest hg
  apply ContextadOuterCharts.cancel (proj (underlying Y)) ((tip Y s).app y) (tipCart _ _ _ _ _ y)
  · exact congrArg (power S j).dest.map hg
  · change J.map (q₁ ≫ b) ≫ (tip Y s).app y = J.map (U.map a ≫ q₂) ≫ (tip Y s).app y
    rw [Functor.map_comp,Functor.map_comp,Category.assoc,Category.assoc,show J.map b ≫ _ = _ from tipFactor c Y y]
    apply Aligned.eq
    apply (AmbientMateCalculus.factor _ _ r.grade r.leg f.hom x).trans
    apply Aligned.symm
    apply ((NativeCube.functorAlign (actionLeaf _ (totalStrong f.hom) (strongOver f.hom)) a).comp (AmbientMateCalculus.factor _ _ s.grade s.leg f.hom x)).trans
    exact NativeCube.ofEq ((V.map_comp _ _).symm.trans (congrArg V.map (tipFactor c X x)))
theorem invSquare :
    (comparison S r p f).inv ≫ AmbientBicategory.map S i f ◁ (cmp c p q Y).hom =
      (cmp c p q X).hom ▷ AmbientBicategory.map S j f ≫ (comparison S s q f).inv := by
  apply extRaw S; intro x
  rw [compAt,compAt]
  have l := (preAt S _ _ x).trans ((cmpAt c p q _).trans (ContextadPayloadModification.appChange _ (Functor.congr_obj (mapEncode S f i) x)))
  have r' := (postAt S (cmp c p q X).hom (AmbientBicategory.map S j f) x).trans
    ((NativeCube.functorAlign (mapEncode S f j) _).trans ((cmpAt c p q x).map _))
  exact ((AmbientComparisonRead.comparisonAt S r p f x).comp l).trans
    ((NativeCube.ofEq (rawSquare c f x)).trans (r'.comp (AmbientComparisonRead.comparisonAt S s q f x)).symm)
noncomputable def modification : StrongTrans.Modification (AmbientPseudonaturality.operation S r p) (AmbientPseudonaturality.operation S s q) where
  app X := (cmp c p q X).hom
  naturality {X Y} f := unbend (comparison S r p f) (comparison S s q f) _ _ (invSquare c p q f)
noncomputable def iso :
    AmbientPseudonaturality.operation S r p ≅ AmbientPseudonaturality.operation S s q :=
  StrongTrans.isoMk (fun X => cmp c p q X) (fun f => unbend (comparison S r p f) (comparison S s q f) _ _ (invSquare c p q f))
end ContextualComposition.GrothendieckStep.AmbientNativeModification
