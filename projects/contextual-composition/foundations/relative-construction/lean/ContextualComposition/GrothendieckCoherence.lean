module
public import ContextualComposition.GrothendieckStep
@[expose] public section
namespace ContextualComposition.GrothendieckStep
open CategoryTheory CategoryTheory.Functor Opposite
universe uB vB uK vK uL vL uM vM uY vY
variable {B : Type uB} [Category.{vB} B] {K : Type uK} [Category.{vK} K]
variable {L : Type uL} [Category.{vL} L] {M : Type uM} [Category.{vM} M]
variable (Y : Bᵒᵖ ⥤ Cat.{vY,uY}) (e : K ⥤ B) (d : L ⥤ B) (c : M ⥤ B)
variable (r : K ⥤ L) (s : L ⥤ M) (l : r ⋙ d ⟶ e) (m : s ⋙ c ⟶ d)

/-- Paste comparisons in the direction of maps of extended bases. -/
def pasteLift : (r ⋙ s) ⋙ c ⟶ e := whiskerLeft r m ≫ l

theorem restrictionCell_id : restrictionCell Y e e (𝟭 K) (𝟙 e) = 𝟙 (diagram Y e) := by
  apply NatTrans.ext
  funext p
  change (Y ⋙ Cat.opFunctor).map (𝟙 _) = _
  exact (Y ⋙ Cat.opFunctor).map_id _

theorem restrictionCell_paste :
    restrictionCell Y e c (r ⋙ s) (pasteLift e d c r s l m) =
      restrictionCell Y e d r l ≫ whiskerLeft r.op (restrictionCell Y d c s m) := by
  apply NatTrans.ext
  funext p
  change (Y ⋙ Cat.opFunctor).map ((_ ≫ _).op) = _
  rw [op_comp, Functor.map_comp]
  rfl

theorem restrict_id : restrict Y e e (𝟭 K) (𝟙 e) = 𝟭 _ := by
  unfold restrict
  rw [restrictionCell_id, Grothendieck.map_id_eq]
  rfl

theorem restrict_paste :
    restrict Y e c (r ⋙ s) (pasteLift e d c r s l m) =
      restrict Y e d r l ⋙ restrict Y d c s m := by
  unfold restrict
  rw [restrictionCell_paste, Grothendieck.map_comp_eq]
  rfl

theorem restrict_congr {r₁ r₂ : K ⥤ L} {l₁ : r₁ ⋙ d ⟶ e} {l₂ : r₂ ⋙ d ⟶ e}
    (hr : r₁ = r₂) (hl : HEq l₁ l₂) : restrict Y e d r₁ l₁ = restrict Y e d r₂ l₂ := by
  subst r₂
  cases eq_of_heq hl
  rfl

namespace Endpoints
variable (P : Endpoints.{uB,vB,uK,vK} B)
/-- Laws on the input endpoint comparisons only. Heterogeneous equality transports
along the grade presheaf laws; no equality of total restriction functors is assumed. -/
structure Split : Prop where
  lift_id : ∀ A : B, HEq (P.lift (𝟙 A)) (𝟙 (P.extend A))
  lift_comp : ∀ {A A' A'' : B} (u : A' ⟶ A) (v : A'' ⟶ A'),
    HEq (P.lift (v ≫ u)) (pasteLift _ _ _ _ _ (P.lift u) (P.lift v))

variable (S : Split P)
include S
theorem baseRestrict_id (A : B) : P.baseRestrict Y (𝟙 A) = 𝟭 _ :=
  (restrict_congr Y _ _ (congrArg Cat.Hom.toFunctor (P.grades.map_id (op A)))
    (S.lift_id A)).trans (restrict_id Y _)

theorem baseRestrict_comp {A A' A'' : B} (u : A' ⟶ A) (v : A'' ⟶ A') :
    P.baseRestrict Y (v ≫ u) = P.baseRestrict Y u ⋙ P.baseRestrict Y v :=
  (restrict_congr Y _ _ (congrArg Cat.Hom.toFunctor (P.grades.map_comp u.op v.op))
    (S.lift_comp u v)).trans (restrict_paste Y _ _ _ _ _ _ _)

/-- The one-step extension now has all the structure of an ordinary Cat-valued presheaf. -/
def extensionPresheaf : Bᵒᵖ ⥤ Cat where
  obj A := Cat.of (Total Y (P.extend A.unop))
  map u := (P.baseRestrict Y u.unop).toCatHom
  map_id A := congrArg Functor.toCatHom (P.baseRestrict_id Y S A.unop)
  map_comp u v := congrArg Functor.toCatHom (P.baseRestrict_comp Y S u.unop v.unop)
/-- Formula on the actual homs. The two transports are forced by the object
components of the same strict functor equality, not independent comparison data. -/
theorem baseRestrict_comp_arrow {A A' A'' : B} (u : A' ⟶ A) (v : A'' ⟶ A')
    {x y : Total Y (P.extend A)} (f : x ⟶ y) :
    (P.baseRestrict Y (v ≫ u)).map f =
      eqToHom (Functor.congr_obj (P.baseRestrict_comp Y S u v) x) ≫
      (P.baseRestrict Y v).map ((P.baseRestrict Y u).map f) ≫
      eqToHom (Functor.congr_obj (P.baseRestrict_comp Y S u v) y).symm := by
  exact Functor.congr_hom (P.baseRestrict_comp Y S u v) f
end Endpoints

namespace Families
theorem splitEndpoints : endpoints.Split where
  lift_id _ := HEq.rfl
  lift_comp _ _ := HEq.rfl
def collapse : Bool ⟶ Unit := TypeCat.ofHom (fun _ => ())

theorem twice_payload (b t : Bool) :
    (payloadMap ((endpoints.baseRestrict presheaf collapse).map
      ((endpoints.baseRestrict presheaf (selectPoint b)).map sampleArrow)) ⟨t,()⟩).hom () = b := rfl

theorem composite_payload (b t : Bool) :
    (payloadMap ((endpoints.baseRestrict presheaf (collapse ≫ selectPoint b)).map sampleArrow)
      ⟨t,()⟩).hom () = b := rfl
end Families
end ContextualComposition.GrothendieckStep
