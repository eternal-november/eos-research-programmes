module
public import ContextualComposition.RelativeTensorInputDiagram
public import ContextualComposition.RelativeTensorOutputDiagram
public import ContextualComposition.RelativeTensorCommaSquare
public import ContextualComposition.EndpointNormalization

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Factorization Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

/-- Pair two pseudofunctors with a common source, keeping both compositor isomorphisms. -/
def pair {A B C : Type*} [Bicategory A] [Bicategory B] [Bicategory C] (P : A ⥤ᵖ B) (Q : A ⥤ᵖ C) : A ⥤ᵖ (B × C) where
  obj a := (P.obj a,Q.obj a)
  map f := ⟨P.map f,Q.map f⟩
  map₂ η := ⟨P.map₂ η,Q.map₂ η⟩
  mapId a := (P.mapId a).prod (Q.mapId a)
  mapComp f g := (P.mapComp f g).prod (Q.mapComp f g)
  map₂_id f := Prod.ext (P.map₂_id f) (Q.map₂_id f)
  map₂_comp η θ := Prod.ext (P.map₂_comp η θ) (Q.map₂_comp η θ)
  map₂_whisker_left := by intros; exact Prod.ext (P.map₂_whisker_left ..) (Q.map₂_whisker_left ..)
  map₂_whisker_right := by intros; exact Prod.ext (P.map₂_whisker_right ..) (Q.map₂_whisker_right ..)
  map₂_associator f g h := Prod.ext (P.map₂_associator f g h) (Q.map₂_associator f g h)
  map₂_left_unitor f := Prod.ext (P.map₂_left_unitor f) (Q.map₂_left_unitor f)
  map₂_right_unitor f := Prod.ext (P.map₂_right_unitor f) (Q.map₂_right_unitor f)

universe vK vL vC uK uL uC
variable (C : Type uC) [Category.{vC} C]
def factorDiagram := pair (Input.diagram.{vK,vL,vC,uK,uL,uC} C) (Output.diagram.{vK,vL,vC,uK,uL,uC} C)
def tensorDiagram := (factorDiagram.{vK,vL,vC,uK,uL,uC} C).comp bifunctor
def largeTensor := (tensorDiagram.{vK,vL,vC,uK,uL,uC} C).comp Endpoint.UniverseLift.pseudofunctor.{max vK vL vC uK uL uC}

section ComponentsOfComposite
variable {I : Type*} [Bicategory I] {J : Type*} [Category* J] (P : I ⥤ᵖ Factors.{_,_,vK,uK,vL,uL} J)
variable {a b c : I}
abbrev fibreCell {p q : P.obj a ⟶ P.obj b} (n : p ⟶ q) (x : Tensor (P.obj a).1 (P.obj a).2) :=
  (insertion (P.obj b).1 (P.obj b).2 x.as.mid).map (productMap ((n.1.as.app ⟨x.as.mid⟩).toNatTrans.app x.as.first)
    ((n.2.as.app ⟨op x.as.mid⟩).toNatTrans.app x.as.second))

theorem mapCell_app {p q : a ⟶ b} (n : p ⟶ q) (x : Tensor (P.obj a).1 (P.obj a).2) :
    ((P.comp bifunctor).map₂ n).toNatTrans.app x = fibreCell P (P.map₂ n) x := bothCell_app (P.map₂ n) x

theorem mapUnit_app (a : I) (x : Tensor (P.obj a).1 (P.obj a).2) :
    ((P.comp bifunctor).mapId a).hom.toNatTrans.app x = fibreCell P (P.mapId a).hom x := by
  change (bothCell (P.mapId a).hom).app x ≫ (bothIdentityIso (P.obj a)).hom.toNatTrans.app x = _
  rw [both_identity_app]
  erw [Category.comp_id]
  exact bothCell_app _ _

theorem mapComp_app (p : a ⟶ b) (q : b ⟶ c) (x : Tensor (P.obj a).1 (P.obj a).2) :
    ((P.comp bifunctor).mapComp p q).hom.toNatTrans.app x = fibreCell P (P.mapComp p q).hom x := by
  change (bothCell (P.mapComp p q).hom).app x ≫ (bothCompositeIso (P.map p) (P.map q)).hom.toNatTrans.app x = _
  rw [both_composite_app]
  erw [Category.comp_id]
  exact bothCell_app _ _
end ComponentsOfComposite

section Components
variable {C} {A B D : Endpoint.Presentation.{vK,vL,vC,uK,uL,uC} C}

theorem decodedChoice {T U : A ⟶ B} (m : T ⟶ U) (s : Carrier A.source A.target) :
    let n := (decode B.source B.target).map (((tensorDiagram C).map₂ m).toNatTrans.app s)
    n.left = m.input.hom.app s.as.first.left ∧ n.right = m.output.hom.app s.as.second.right := by
  dsimp only
  rw [show ((tensorDiagram C).map₂ m).toNatTrans.app s = _ from mapCell_app (factorDiagram.{vK,vL,vC,uK,uL,uC} C) (a := A) (b := B) m s]
  exact decode_grades _ _ _ _

theorem decodedUnit (A : Endpoint.Presentation.{vK,vL,vC,uK,uL,uC} C) (s : Carrier A.source A.target) :
    let n := (decode A.source A.target).map (((tensorDiagram C).mapId A).hom.toNatTrans.app s)
    n.left = 𝟙 s.as.first.left ∧ n.right = 𝟙 s.as.second.right := by
  dsimp only
  rw [show ((tensorDiagram C).mapId A).hom.toNatTrans.app s = _ from mapUnit_app (factorDiagram.{vK,vL,vC,uK,uL,uC} C) A s]
  exact decode_grades _ _ _ _

theorem decodedComposite (T : A ⟶ B) (U : B ⟶ D) (s : Carrier A.source A.target) :
    let n := (decode D.source D.target).map (((tensorDiagram C).mapComp T U).hom.toNatTrans.app s)
    n.left = 𝟙 (U.input.obj (T.input.obj s.as.first.left)) ∧ n.right = 𝟙 (U.output.obj (T.output.obj s.as.second.right)) := by
  dsimp only
  rw [show ((tensorDiagram C).mapComp T U).hom.toNatTrans.app s = _ from mapComp_app (factorDiagram.{vK,vL,vC,uK,uL,uC} C) (a := A) (b := B) (c := D) T U s]
  exact decode_grades _ _ _ _

end Components
end ContextualComposition.RelativeTensor.Presented
