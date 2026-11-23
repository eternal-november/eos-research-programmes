module
public import ContextualComposition.RelativeTensorAssociatorLastCells
public import ContextualComposition.PointwisePseudonaturalEquivalence

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe vB uB vC uC vD uD vX uX vM uM vN uN
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))

abbrev leftBrackets := leftInner (leftInner X M) N
abbrev middleBrackets := leftInner X (middleComposite M N)
abbrev componentAt (d : LocallyDiscrete D) := associate X M (N.obj d)

def fourthIndexSquare {d e : LocallyDiscrete D} (v : d ⟶ e) :
    (leftBrackets X M N).map v ≫ (componentAt X M N e).toCatHom ≅
      (componentAt X M N d).toCatHom ≫ (middleBrackets X M N).map v :=
  Cat.Hom.isoMk (eqToIso (last_naturality X M (N.map v)))

@[simp] theorem fourthIndexSquare_app {d e : LocallyDiscrete D} (v : d ⟶ e) (z : (leftBrackets X M N).obj d) :
    (fourthIndexSquare X M N v).hom.toNatTrans.app z = 𝟙 _ := by
  change (eqToHom (last_naturality X M (N.map v))).app z = _
  rw [eqToHom_app]; rfl

private theorem dropOne {K : Type*} [Category* K] {x y : K} (f : x ⟶ y) (k : y ⟶ y) (h : k = 𝟙 _) : f ≫ k = f := by simp [h]
private theorem dropTwo {K : Type*} [Category* K] {x y : K} (f : x ⟶ y) (k : y ⟶ y) (h : k = 𝟙 _) : (f ≫ k) ≫ 𝟙 _ = f := by simp [h]

private theorem middleId (d : LocallyDiscrete D) (b : LocallyDiscrete Bᵒᵖ)
    (z : Tensor ((Middle.transpose M).obj b) (N.obj d)) :
    (((middleComposite M N).mapId d).hom.as.app b).toNatTrans.app z =
      (Second.mapCell (F := (Middle.transpose M).obj b) (N.mapId d).hom.as).app z := by
  exact dropTwo ((Second.mapCell (F := (Middle.transpose M).obj b) (N.mapId d).hom.as).app z) _
    (Second.identity_hom_app ((Middle.transpose M).obj b) (N.obj d) z)

private theorem middleComp {d e k : LocallyDiscrete D} (v : d ⟶ e) (w : e ⟶ k) (b : LocallyDiscrete Bᵒᵖ)
    (z : Tensor ((Middle.transpose M).obj b) (N.obj d)) :
    (((middleComposite M N).mapComp v w).hom.as.app b).toNatTrans.app z =
      (Second.mapCell (F := (Middle.transpose M).obj b) (N.mapComp v w).hom.as).app z := by
  exact dropTwo ((Second.mapCell (F := (Middle.transpose M).obj b) (N.mapComp v w).hom.as).app z) _
    (Second.composite_hom_app ((Middle.transpose M).obj b) (N.map v) (N.map w) z)

theorem outerUnit (d : LocallyDiscrete D) (z : (leftBrackets X M N).obj d) :
    (componentAt X M N d).map (((leftBrackets X M N).mapId d).hom.toNatTrans.app z) =
      ((middleBrackets X M N).mapId d).hom.toNatTrans.app ((componentAt X M N d).obj z) := by
  change (associate X M (N.obj d)).map
    ((Second.mapCell (N.mapId d).hom.as).app z ≫ (Second.identityIso _ _).hom.toNatTrans.app z) =
    (Second.mapCell (F := X) ((middleComposite M N).mapId d).hom.as).app ((componentAt X M N d).obj z) ≫ (Second.identityIso X _).hom.toNatTrans.app ((componentAt X M N d).obj z)
  erw [Second.identity_hom_app,Second.identity_hom_app,Category.comp_id,Category.comp_id]
  erw [last_cell_app X M (N.mapId d).hom]
  change (insertion _ _ _).map (productMap (𝟙 _) _) = (insertion _ _ _).map (productMap (𝟙 _) _)
  congr 2
  exact (middleId M N d _ _).symm

theorem outerComp {d e k : LocallyDiscrete D} (v : d ⟶ e) (w : e ⟶ k) (z : (leftBrackets X M N).obj d) :
    (componentAt X M N k).map (((leftBrackets X M N).mapComp v w).hom.toNatTrans.app z) =
      ((middleBrackets X M N).mapComp v w).hom.toNatTrans.app ((componentAt X M N d).obj z) := by
  let E := componentAt X M N k
  let z' := (componentAt X M N d).obj z
  let m := (N.mapComp v w).hom
  let n := ((middleComposite M N).mapComp v w).hom
  have h := last_cell_app X M m z
  have h' := congrArg (fun q => (insertion X ((middleComposite M N).obj k) z'.as.mid).map (productMap (𝟙 z'.as.first) q))
    (middleComp M N v w ⟨op z'.as.mid⟩ z'.as.second)
  exact (congrArg E.map (dropOne ((Second.mapCell (F := leftInner X M) m.as).app z) _
    (Second.composite_hom_app (leftInner X M) (N.map v) (N.map w) z))).trans
    (h.trans (h'.symm.trans (dropOne ((Second.mapCell (F := X) n.as).app z') _
      (Second.composite_hom_app X ((middleComposite M N).map v) ((middleComposite M N).map w) z')).symm))

private theorem unitPad {K : Type*} [Category* K] {x y : K} {c : x ⟶ x} {i j : x ⟶ y}
    (hc : c = 𝟙 _) (h : i = j) : c ≫ j = i ≫ 𝟙 _ ≫ 𝟙 _ := by simp [hc,h]
private theorem compPad {K L : Type*} [Category* K] [Category* L] (F : K ⥤ L) {x : L} {y : K}
    {j : x ⟶ x} {k : F.obj y ⟶ F.obj y} {l : y ⟶ y} {p q : x ⟶ F.obj y}
    (hj : j = 𝟙 _) (hk : k = 𝟙 _) (hl : l = 𝟙 _) (hp : p = q) :
    j ≫ q = p ≫ 𝟙 _ ≫ k ≫ 𝟙 _ ≫ F.map l ≫ 𝟙 _ := by simp [hj,hk,hl,hp]

set_option maxHeartbeats 1000000 in
/-- Reassociate the first three factors as a strong transformation over the remaining covariant boundary. -/
def outerAssociator : leftBrackets X M N ⟶ middleBrackets X M N where
  app d := (componentAt X M N d).toCatHom
  naturality v := fourthIndexSquare X M N v
  naturality_naturality {d e j k} h := by
    obtain rfl := LocallyDiscrete.eq_of_hom h
    obtain rfl := Subsingleton.elim h (𝟙 j)
    rw [PrelaxFunctor.map₂_id,PrelaxFunctor.map₂_id]
    simp
  naturality_id d := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (fourthIndexSquare X M N (𝟙 d)).hom.toNatTrans.app z ≫ _ =
      (componentAt X M N d).map _ ≫ 𝟙 _ ≫ 𝟙 _
    exact unitPad (fourthIndexSquare_app X M N (𝟙 d) z) (outerUnit X M N d z)
  naturality_comp {d e k} v w := by
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (fourthIndexSquare X M N (v ≫ w)).hom.toNatTrans.app z ≫ _ =
      (componentAt X M N k).map _ ≫ 𝟙 _ ≫ (fourthIndexSquare X M N w).hom.toNatTrans.app _ ≫
      𝟙 _ ≫ ((middleBrackets X M N).map w).toFunctor.map ((fourthIndexSquare X M N v).hom.toNatTrans.app z) ≫ 𝟙 _
    exact compPad ((middleBrackets X M N).map w).toFunctor (fourthIndexSquare_app X M N (v ≫ w) z)
      (fourthIndexSquare_app X M N w (((leftBrackets X M N).map v).toFunctor.obj z))
      (fourthIndexSquare_app X M N v z) (outerComp X M N v w z)

noncomputable def outerEquivalence : Bicategory.Equivalence (leftBrackets X M N) (middleBrackets X M N) := by
  letI (d : LocallyDiscrete D) : ((outerAssociator X M N).app d).toFunctor.IsEquivalence :=
    (associator X M (N.obj d)).isEquivalence_functor
  exact PseudonaturalInverse.equivalence (outerAssociator X M N)

section Whisker
universe vZ uZ
variable (Z : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vZ,uZ})

/-- The first edge of the three-step pentagon route is defined on the native fourfold quotient. -/
def firstPentagonEdge : farLeft X M N Z ⥤ innerLeft X M N Z := mapFirst (G := Z) (outerAssociator X M N)

end Whisker
end ContextualComposition.RelativeTensor.Iterated
