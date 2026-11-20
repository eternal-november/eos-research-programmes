module
public import ContextualComposition.AmbientComparisonRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientOperationLaws
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells ContextadWeakAction ContextadWeakWeight AmbientComparisonRead
open AmbientBicategory AmbientCoordinates ContextadLawTransport ContextadModification NativeBlocks WordTrace CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {X Y Z : Obj.{u,v} B} {i j : Nat}
variable (r : ContextadRoutes.Map S i j) (p : gradeCart r)
theorem before {a b : X ⟶ Y} (t : a ⟶ b) (x) :
    Aligned (atRaw S (oper S r p X ◁ cell S j t) x) ((endpointCell (power S j).dest t.hom.as).app ((raw (underlying X) r).obj x)) :=
  (preAt S _ _ x).trans ((modAt S t j _).trans (ContextadPayloadModification.appChange _ (Functor.congr_obj (opEncode S r p X) x)))
theorem after {a b : X ⟶ Y} (t : a ⟶ b) (x) :
    Aligned (atRaw S (cell S i t ▷ oper S r p Y) x) ((raw (underlying Y) r).map ((endpointCell (power S i).dest t.hom.as).app x)) :=
  (postAt S _ _ x).trans ((NativeCube.functorAlign (opEncode S r p Y) _).trans ((modAt S t i x).map _))
theorem modification {a b : X ⟶ Y} (t : a ⟶ b) :
    (comparison S r p a).inv ≫ cell S i t ▷ oper S r p Y = oper S r p X ◁ cell S j t ≫ (comparison S r p b).inv := by
  apply extRaw S; intro x
  rw [compAt,compAt]
  exact ((comparisonAt S r p a x).comp (after S r p t x)).trans
    ((NativeCube.ofEq (AmbientMateCalculus.modificationSquare _ _ _ _ t.hom.as x)).trans ((before S r p t x).comp (comparisonAt S r p b x)).symm)
theorem pureCmpId (X : Obj.{u,v} B) (x) : Pure (atRaw S (comparison S r p (𝟙 X)).inv x) := by
  apply AmbientMateCalculus.pureOfAligned (comparisonAt S r p (𝟙 X) x)
  change Pure ((AmbientMateCalculus.q _ _ _ _ (𝟙 (underlying X).toPseudofunctor')).app x)
  rw [AmbientMateCalculus.idSquare]; exact ⟨_,eqToHom_app _ _⟩
theorem identityEq (X : Obj.{u,v} B) : AmbientBicategory.map S i (𝟙 X) ≫ oper S r p X = oper S r p X ≫ AmbientBicategory.map S j (𝟙 X) := by
  rw [show AmbientBicategory.map S i (𝟙 X) = 𝟙 _ from (action S i).map_id X,
    show AmbientBicategory.map S j (𝟙 X) = 𝟙 _ from (action S j).map_id X,Category.id_comp,Category.comp_id]
theorem isoPure {f g : obj S i X ⟶ obj S j Y} (c : f ≅ g) (h : f = g) (q : ∀ x, Pure (atRaw S c.inv x)) : c = eqToIso h := by
  apply Iso.ext_inv
  exact extRaw S (fun x => NativeCube.ofEq (pureEq (q x) (castAt S h.symm x)))
theorem identity (X : Obj.{u,v} B) : comparison S r p (𝟙 X) = eqToIso (identityEq S r p X) :=
  isoPure S _ _ (pureCmpId S r p X)
variable (a : X ⟶ Y) (b : Y ⟶ Z)
noncomputable abbrev cmpL := whiskerLeftIso (AmbientBicategory.map S i a) (comparison S r p b)
noncomputable abbrev cmpR := whiskerRightIso (comparison S r p a) (AmbientBicategory.map S j b)
theorem face₀ : AmbientBicategory.map S i (a ≫ b) ≫ oper S r p Z =
    AmbientBicategory.map S i a ≫ (AmbientBicategory.map S i b ≫ oper S r p Z) := by rw [AmbientBicategory.comp,Category.assoc]
theorem face₁ : AmbientBicategory.map S i a ≫ (oper S r p Y ≫ AmbientBicategory.map S j b) =
    (AmbientBicategory.map S i a ≫ oper S r p Y) ≫ AmbientBicategory.map S j b := Category.assoc .. |>.symm
theorem face₂ : (oper S r p X ≫ AmbientBicategory.map S j a) ≫ AmbientBicategory.map S j b =
    oper S r p X ≫ AmbientBicategory.map S j (a ≫ b) := by rw [AmbientBicategory.comp,Category.assoc]
noncomputable def paste := eqToIso (face₀ S r p a b) ≪≫ cmpL S r p a b ≪≫ eqToIso (face₁ S r p a b) ≪≫ cmpR S r p a b ≪≫ eqToIso (face₂ S r p a b)
theorem leftPart (x) : Aligned (atRaw S (cmpL S r p a b).inv x)
    ((q S r b).app ((atEndpoint a.hom (power S i).dest).obj x)) :=
  (preAt S _ _ x).trans ((comparisonAt S r p b _).trans (ContextadPayloadModification.appChange _ (Functor.congr_obj (mapEncode S a i) x)))
theorem rightPart (x) : Aligned (atRaw S (cmpR S r p a b).inv x)
    ((atEndpoint b.hom (power S j).dest).map ((q S r a).app x)) :=
  (postAt S _ _ x).trans ((NativeCube.functorAlign (mapEncode S b j) _).trans ((comparisonAt S r p a x).map _))
theorem trimFive {C : Type*} [Category* C] {a b c d e f : C} (i : a ⟶ b) (j₁ : b ⟶ c) (k : c ⟶ d) (j₂ : d ⟶ e) (l : e ⟶ f)
    (u : Pure i) (v : Pure k) (w : Pure l) {b' c' e' : C} {t : b' ⟶ c'} {s : c' ⟶ e'} (h : Aligned j₁ t) (z : Aligned j₂ s) :
    Aligned ((((i ≫ j₁) ≫ k) ≫ j₂) ≫ l) (t ≫ s) := by
  obtain ⟨rfl,rfl⟩ := u; obtain ⟨rfl,rfl⟩ := v; obtain ⟨rfl,rfl⟩ := w
  simpa using h.comp z
theorem composition : comparison S r p (a ≫ b) = paste S r p a b := by
  apply Iso.ext_inv
  apply extRaw S; intro x
  apply (comparisonAt S r p (a ≫ b) x).trans
  change Aligned ((AmbientMateCalculus.q _ _ _ _ (a.hom.vcomp b.hom)).app x) _
  rw [AmbientMateCalculus.compSquare]
  apply (AmbientMateCalculus.doubledAt _ _ _ _ _ _ _).trans
  apply Aligned.symm
  simp only [paste,Iso.trans_inv,eqToIso.inv,compAt]
  exact trimFive _ _ _ _ _ (castAt S _ x) (castAt S _ x) (castAt S _ x) (rightPart S r p a b x) (leftPart S r p a b x)
end ContextualComposition.GrothendieckStep.AmbientOperationLaws
