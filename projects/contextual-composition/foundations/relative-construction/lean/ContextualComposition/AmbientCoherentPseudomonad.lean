module
public import ContextualComposition.AmbientAssociativity
public import ContextualComposition.AmbientLeftSquare
public import ContextualComposition.AmbientRightSquare
public import ContextualComposition.AmbientTriangle
public import ContextualComposition.AmbientPentagon
public import ContextualComposition.AmbientMonadMapRead
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCoherentPseudomonad
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalNaturality AmbientHorizontalDiagrams
open ContextadNativeLaws ContextadSchedule AmbientCoordinates
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
-- The carrier and the unit/multiplication maps are fixed rather than existential:
-- the exported faces cannot be satisfied by choosing unrelated maps or constraints.
structure Laws (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m) : Prop where
  left_natural : ∀ {X Y : Obj.{u,v} B} (f : X ⟶ Y), Left S d m C f
  right_natural : ∀ {X Y : Obj.{u,v} B} (f : X ⟶ Y), Right S d m C f
  assoc_natural : ∀ {X Y : Obj.{u,v} B} (f : X ⟶ Y), Assoc S d m C f
  triangle : ∀ X : Obj.{u,v} B, Triangle S d m C X
  pentagon : ∀ X : Obj.{u,v} B, Pentagon S d m C X
structure Data where
  unit : ContextadUnit.Data P
  mult : ContextadTotal.Native S
  constraints : Constraints unit mult
  laws : Laws S unit mult constraints
variable {S}
def build (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m) (h : Coherent d m C) : Data S where
  unit := d
  mult := m
  constraints := C
  laws := ⟨fun f => AmbientLeftSquare.original f d m C,fun f => AmbientRightSquare.original f d m C,
    fun f => AmbientAssociativity.original f m d C,fun X => AmbientTriangle.original X d m C h.triangle,
    fun X => AmbientPentagon.original X d m C h.pentagon⟩
variable (T : Data S)
noncomputable abbrev endofunctor := (AmbientBicategory.action S 1).toPseudofunctor
noncomputable abbrev unitMap := AmbientMonadMaps.eta S T.unit
noncomputable abbrev multMap := AmbientMonadMaps.mu S T.mult
noncomputable abbrev leftIso (X : Obj.{u,v} B) := left S X T.unit T.mult T.constraints
noncomputable abbrev rightIso (X : Obj.{u,v} B) := right S X T.unit T.mult T.constraints
noncomputable abbrev assocIso (X : Obj.{u,v} B) := assoc S X T.unit T.mult T.constraints
end ContextualComposition.GrothendieckStep.AmbientCoherentPseudomonad
