module
public import ContextualComposition.TelescopeGradeChange
public import ContextualComposition.AmbientBlockCells

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeGradeChange

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open FibreValue SpanApex BoundaryPaste ContextadWeakAction ContextadAmbientPayload AmbientBlockCells
open scoped CategoryTheory.Pseudofunctor.StrongTrans

set_option backward.isDefEq.respectTransparency false
universe u v k w l j
variable {B : Type u} [Category.{v} B] {K : Type k} [Category.{w} K] {L : Type l} [Category.{j} L]
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'}
variable (m : StrongTrans.Modification a b) (r : K ⥤ L) (d : L ⥤ B) {e : K ⥤ B} (h : r ⋙ d = e)

/-- The strict grade-change square transports a directed ambient modification across both of its boundaries. -/
theorem totalMap_modification :
    whiskerLeft (SpanPayload.totalMap Y r d h) (endpointCell d m) ≫ eqToHom (totalMap_payload b r d h) =
      eqToHom (totalMap_payload a r d h) ≫ whiskerRight (endpointCell e m) (SpanPayload.totalMap Z r d h) := by
  subst e
  apply NatTrans.ext
  funext x
  apply (intoPullback (projectionData Z) d).map_injective
  apply Limits.CategoricalPullback.hom_ext
  · change gradeMap (_ ≫ _) = gradeMap (_ ≫ _)
    simp only [grade_comp]
    apply pureEq
    · exact pureComp (endpointOver d m _) (pureMap gradeProjection ⟨_,eqToHom_app _ _⟩)
    · exact pureComp (pureMap gradeProjection ⟨_,eqToHom_app _ _⟩) (pureMap r (endpointOver (r ⋙ d) m x))
  · change (second (projectionData Z) d).map (_ ≫ _) = (second (projectionData Z) d).map (_ ≫ _)
    simp only [Functor.map_comp,eqToHom_app,eqToHom_map,whiskerLeft_app,whiskerRight_app,endpointLeaf]
    change (AmbientBlockCells.tail d m).app _ ≫ eqToHom _ =
      eqToHom _ ≫ (second (projectionData Z) (r ⋙ d)).map ((endpointCell (r ⋙ d) m).app x)
    rw [endpointLeaf]
    simp [AmbientBlockCells.tail,Category.assoc,eqToHom_app]
    rfl

section Coproduct

open CoproductSpan TelescopeSquares
universe t v' u'
variable {I : Type t} {C : I → Type u'} [∀ n, Category.{v'} (C n)]
variable (legs : ∀ n, C n ⥤ B)

private theorem totalMap_modification_app (x : Total Y e) :
    Aligned ((endpointCell d m).app ((SpanPayload.totalMap Y r d h).obj x))
      ((SpanPayload.totalMap Z r d h).map ((endpointCell e m).app x)) := by
  refine ⟨Functor.congr_obj (totalMap_payload a r d h) x,Functor.congr_obj (totalMap_payload b r d h) x,?_⟩
  simpa only [NatTrans.comp_app,whiskerLeft_app,whiskerRight_app,eqToHom_app] using
    NatTrans.congr_app (totalMap_modification m r d h) x

/-- The directed modification on the coproduct of the weighted categories acts on each tag by its endpoint lift. -/
noncomputable abbrev taggedModification :
    ZeroPower.Sum.map (fun n => atEndpoint a (legs n)) ⟶ ZeroPower.Sum.map (fun n => atEndpoint b (legs n)) :=
  Sigma.natTrans.sigma (fun n => endpointCell (legs n) m)

/-- The assembled gather square is natural in arbitrary ambient modifications. -/
theorem gather_modification :
    whiskerLeft (Distribute.gather Y legs) (endpointCell (Sigma.desc legs) m) ≫ eqToHom (TelescopeGradeChange.gather_payload b legs) =
      eqToHom (TelescopeGradeChange.gather_payload a legs) ≫ whiskerRight (taggedModification m legs) (Distribute.gather Z legs) := by
  apply NatTrans.ext
  funext ⟨n,x⟩
  simp only [NatTrans.comp_app,whiskerLeft_app,whiskerRight_app,eqToHom_app]
  dsimp only [Distribute.gather,Distribute.tag,taggedModification,Sigma.natTrans.sigma,Sigma.desc_map_mk,Sigma.desc_obj]
  exact (totalMap_modification_app m (Sigma.incl n) (Sigma.desc legs) (e := legs n) rfl x).comm

variable (src dst : ∀ n, C n ⥤ B) (A : B)

/-- Naturality of the actual coproduct-to-whole-span comparison follows by pasting the tag and pack squares. -/
theorem compare_modification :
    whiskerLeft (compare src dst A Y) (endpointCell (wholeLeg src dst A) m) ≫ eqToHom (TelescopeGradeChange.compare_payload b src dst A) =
      eqToHom (TelescopeGradeChange.compare_payload a src dst A) ≫ whiskerRight (taggedModification m (leg src dst A)) (compare src dst A Z) := by
  apply NatTrans.ext
  funext ⟨n,x⟩
  have tag := totalMap_modification_app m (Sigma.incl n) (Sigma.desc (leg src dst A)) (e := leg src dst A n) rfl x
  have whole := totalMap_modification_app m (pack src A) (wholeLeg src dst A) (over src dst A) ((Distribute.tag Y (leg src dst A) n).obj x)
  simp only [NatTrans.comp_app,whiskerLeft_app,whiskerRight_app,eqToHom_app]
  dsimp only [CoproductSpan.compare,Functor.comp_obj,Functor.comp_map,Distribute.gather,Distribute.tag,taggedModification,Sigma.natTrans.sigma,Sigma.desc_map_mk,Sigma.desc_obj]
  exact (whole.trans (Aligned.map (weightedPack src dst A Z) tag)).comm

end Coproduct

end ContextualComposition.GrothendieckStep.TelescopeGradeChange
