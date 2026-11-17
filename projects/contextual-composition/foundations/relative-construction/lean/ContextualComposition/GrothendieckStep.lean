module
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Types.Basic
@[expose] public section
namespace ContextualComposition.GrothendieckStep
open CategoryTheory CategoryTheory.Functor Opposite
universe uB vB uK vK uL vL uY vY
variable {B : Type uB} [Category.{vB} B] {K : Type uK} [Category.{vK} K]
variable {L : Type uL} [Category.{vL} L]
variable (Y : Bᵒᵖ ⥤ Cat.{vY,uY}) (e : K ⥤ B)

def diagram : Kᵒᵖ ⥤ Cat.{vY,uY} := e.op ⋙ Y ⋙ Cat.opFunctor

/-- Outer and fibre opposites together give the contravariant category of elements.
The decoded grade and payload arrows below both run in the manuscript directions. -/
abbrev Total := (Grothendieck (diagram Y e))ᵒᵖ

def pair (p : K) (x : Y.obj (op (e.obj p))) : Total Y e :=
  op ⟨op p, op x⟩

def grade (z : Total Y e) : K := z.unop.base.unop
def payload (z : Total Y e) : Y.obj (op (e.obj (grade Y e z))) := z.unop.fiber.unop

variable {Y e}
def gradeMap {x y : Total Y e} (f : x ⟶ y) : grade Y e x ⟶ grade Y e y := f.unop.base.unop
def payloadMap {x y : Total Y e} (f : x ⟶ y) :
    payload Y e x ⟶ (Y.map (e.map (gradeMap f)).op).toFunctor.obj (payload Y e y) :=
  f.unop.fiber.unop

def arrow {x y : Total Y e} (k : grade Y e x ⟶ grade Y e y)
    (h : payload Y e x ⟶ (Y.map (e.map k).op).toFunctor.obj (payload Y e y)) : x ⟶ y :=
  Quiver.Hom.op (show _ ⟶ _ from { base := k.op, fiber := h.op })

def homEquiv (x y : Total Y e) :
    (x ⟶ y) ≃ Σ k : grade Y e x ⟶ grade Y e y,
      (payload Y e x ⟶ (Y.map (e.map k).op).toFunctor.obj (payload Y e y)) where
  toFun f := ⟨gradeMap f, payloadMap f⟩
  invFun f := arrow f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem grade_id (x : Total Y e) : gradeMap (𝟙 x) = 𝟙 _ := rfl

theorem grade_comp {x y z : Total Y e} (f : x ⟶ y) (g : y ⟶ z) :
    gradeMap (f ≫ g) = gradeMap f ≫ gradeMap g := rfl

def gradeProjection : Total Y e ⥤ K where
  obj := grade Y e
  map := gradeMap

theorem comp_target {p q r : K} (k : p ⟶ q) (j : q ⟶ r) (x : Y.obj (op (e.obj r))) :
    (Y.map (e.map k).op).toFunctor.obj ((Y.map (e.map j).op).toFunctor.obj x) =
      (Y.map (e.map (k ≫ j)).op).toFunctor.obj x := by
  rw [e.map_comp, op_comp,Y.map_comp]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem payload_comp {x y z : Total Y e} (f : x ⟶ y) (g : y ⟶ z) :
    payloadMap (f ≫ g) = payloadMap f ≫
      (Y.map (e.map (gradeMap f)).op).toFunctor.map (payloadMap g) ≫
      eqToHom (comp_target (gradeMap f) (gradeMap g) (payload Y e z)) := by
  change (Grothendieck.Hom.fiber (g.unop ≫ f.unop)).unop = _
  rw [Grothendieck.comp_fiber, unop_comp, unop_comp, Category.assoc]
  congr 2
  apply eqToHom_unop

variable (Y e) (d : L ⥤ B) (r : K ⥤ L) (l : r ⋙ d ⟶ e)
/-- The square on grade arrows gives a transformation of diagrams without assuming that
any component of the comparison l is invertible. -/
def restrictionCell : diagram Y e ⟶ r.op ⋙ diagram Y d :=
  whiskerRight (NatTrans.op l) (Y ⋙ Cat.opFunctor)

def restrict : Total Y e ⥤ Total Y d :=
  (Grothendieck.map (restrictionCell Y e d r l) ⋙ Grothendieck.pre (diagram Y d) r.op).op

theorem restrict_pair (p : K) (x : Y.obj (op (e.obj p))) :
    (restrict Y e d r l).obj (pair Y e p x) =
      pair Y d (r.obj p) ((Y.map (l.app p).op).toFunctor.obj x) := rfl

theorem restrict_grade {x y : Total Y e} (f : x ⟶ y) :
    gradeMap ((restrict Y e d r l).map f) = r.map (gradeMap f) := rfl

theorem restrict_projection :
    restrict Y e d r l ⋙ gradeProjection = gradeProjection ⋙ r := rfl

/-- The target type correction is exactly the image of grade naturality in the
category-valued presheaf, not a chosen isomorphism between unrelated payloads. -/
theorem endpoint_square {p q : K} (k : p ⟶ q) (z : Y.obj (op (e.obj q))) :
    (Y.map (l.app p).op).toFunctor.obj ((Y.map (e.map k).op).toFunctor.obj z) =
      (Y.map (d.map (r.map k)).op).toFunctor.obj ((Y.map (l.app q).op).toFunctor.obj z) := by
  have h := congrArg (fun m => (Y.map (Quiver.Hom.op m)).toFunctor.obj z) (l.naturality k)
  simpa only [op_comp,Functor.map_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj,Functor.comp_map] using h.symm

set_option backward.isDefEq.respectTransparency false in
theorem restrict_payload {x y : Total Y e} (f : x ⟶ y) :
    payloadMap ((restrict Y e d r l).map f) =
      (Y.map (l.app (grade Y e x)).op).toFunctor.map (payloadMap f) ≫
        eqToHom (endpoint_square Y e d r l (gradeMap f) (payload Y e y)) := by
  change (Grothendieck.Hom.fiber ((Grothendieck.map (restrictionCell Y e d r l)).map f.unop)).unop = _
  dsimp [Grothendieck.map, payloadMap]
  simp
  rw [unop_comp]
  congr 1
  apply eqToHom_unop

/-- The local base-arrow interface: grade reindexing really comes from an arbitrary
Cat-valued presheaf, and the extension comparison is a natural transformation on its
entire native grade category. No coherence across different base arrows is a field. -/
structure Endpoints (B : Type uB) [Category.{vB} B] where
  grades : Bᵒᵖ ⥤ Cat.{vK,uK}
  extend : ∀ A : B, grades.obj (op A) ⥤ B
  lift : ∀ {A A' : B} (u : A' ⟶ A), (grades.map u.op).toFunctor ⋙ extend A' ⟶ extend A

namespace Endpoints
variable (P : Endpoints.{uB,vB,uK,vK} B) (Y : Bᵒᵖ ⥤ Cat.{vY,uY})
def baseRestrict {A A' : B} (u : A' ⟶ A) :
    Total Y (P.extend A) ⥤ Total Y (P.extend A') :=
  restrict Y _ _ (P.grades.map u.op).toFunctor (P.lift u)

theorem baseRestrict_arrow {A A' : B} (u : A' ⟶ A) {x y : Total Y (P.extend A)} (f : x ⟶ y) :
    (baseRestrict P Y u).map f =
      arrow ((P.grades.map u.op).toFunctor.map (gradeMap f))
        ((Y.map ((P.lift u).app (grade Y _ x)).op).toFunctor.map (payloadMap f) ≫
          eqToHom (endpoint_square Y _ _ _ (P.lift u) (gradeMap f) (payload Y _ y))) := by
  apply (homEquiv _ _).injective
  exact Sigma.ext (restrict_grade Y _ _ _ (P.lift u) f)
    (heq_of_eq (restrict_payload Y _ _ _ (P.lift u) f))
end Endpoints

namespace Families
/-- Families of small types over a small type, with all pointwise functions as arrows. -/
def presheaf : (Type)ᵒᵖ ⥤ Cat.{0,1} where
  obj A := Cat.of (A.unop → Type)
  map {A _} f := (Pi.comap (fun _ : A.unop => Type) (fun a => f.unop a)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

def sumFunctor (A : Type) : presheaf.obj (op A) ⥤ Type where
  obj F := Σ a, F a
  map f := TypeCat.ofHom (fun z => ⟨z.1,(f z.1) z.2⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

def sumLift {A A' : Type} (u : A' ⟶ A) :
    (presheaf.map u.op).toFunctor ⋙ sumFunctor A' ⟶ sumFunctor A where
  app _ := TypeCat.ofHom (fun z => ⟨u z.1,z.2⟩)
  naturality _ _ _ := rfl

def endpoints : Endpoints (Type) where
  grades := presheaf
  extend := sumFunctor
  lift := sumLift


def smallGrade : presheaf.obj (op Bool) := fun _ => Unit
def wideGrade : presheaf.obj (op Bool) := fun _ => Bool
def widen : smallGrade ⟶ wideGrade := fun _ => TypeCat.ofHom (fun _ => true)

def sourcePair : Total presheaf (sumFunctor Bool) :=
  pair _ _ smallGrade (fun _ => Unit)

def targetPair : Total presheaf (sumFunctor Bool) :=
  pair _ _ wideGrade (fun z => if (show Bool from z.2) = true then Bool else Empty)

/-- The target payload depends on the new grade, and the component at a source index
returns the original base point. A wrong-way or endpoint-fixed formula does not typecheck. -/
def sampleArrow : sourcePair ⟶ targetPair :=
  arrow (Y := presheaf) (e := sumFunctor Bool) (x := sourcePair) (y := targetPair) widen
    (fun z => TypeCat.ofHom (fun _ => z.1))

def selectPoint (b : Bool) : Unit ⟶ Bool := TypeCat.ofHom (fun _ => b)

theorem sample_grade (b : Bool) :
    (gradeMap ((endpoints.baseRestrict presheaf (selectPoint b)).map sampleArrow) ()).hom () = true := rfl

theorem sample_payload (b : Bool) :
    (payloadMap ((endpoints.baseRestrict presheaf (selectPoint b)).map sampleArrow) ⟨(),()⟩).hom () = b := rfl

theorem select_no_section (b : Bool) : ¬ ∃ s : Bool ⟶ Unit, s ≫ selectPoint b = 𝟙 _ := by
  rintro ⟨s,h⟩
  have h' := congrArg (fun k : Bool ⟶ Bool => k (!b)) h
  change b = !b at h'
  cases b <;> cases h'

theorem widen_not_iso : ¬ IsIso widen := by
  intro i
  obtain ⟨r,_,h⟩ := i.out
  have h' := congrArg (fun k : wideGrade ⟶ wideGrade => (k false).hom false) h
  exact Bool.noConfusion h'

theorem sample_not_iso : ¬ IsIso sampleArrow := by
  intro h
  let : IsIso sampleArrow := h
  exact widen_not_iso (show IsIso ((gradeProjection (Y := presheaf) (e := sumFunctor Bool)).map sampleArrow) by infer_instance)

end Families
end ContextualComposition.GrothendieckStep
