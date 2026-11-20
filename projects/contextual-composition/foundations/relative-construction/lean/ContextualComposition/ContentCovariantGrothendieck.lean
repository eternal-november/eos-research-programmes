module
public import ContextualComposition.GrothendieckCoherence
public import Mathlib.CategoryTheory.IsoCat
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentCovariantGrothendieck
open CategoryTheory CategoryTheory.Functor Opposite
set_option backward.isDefEq.respectTransparency false
universe u
variable {B : Type u} [Category.{u} B]

abbrev Cov := B ⥤ Cat.{u,u}
abbrev Dual := Bᵒᵖᵒᵖ ⥤ Cat.{u,u}

/-- The fibre opposite decodes the *contravariant constructor on the dual base*.
It is not an opposite of the native content hom-categories. -/
def decode (Y : Dual (B := B)) : Cov (B := B) := opOp B ⋙ Y ⋙ Cat.opFunctor
def encode (Y : Cov (B := B)) : Dual (B := B) := unopUnop B ⋙ Y ⋙ Cat.opFunctor

variable (P : Endpoints.{u,u,u,u} Bᵒᵖ)
def grades : Cov (B := B) := decode P.grades
def dest (A : B) : (grades P).obj A ⥤ B := (P.extend (op A)).leftOp

def lift {A D : B} (v : A ⟶ D) :
    dest P A ⟶ ((grades P).map v).toFunctor ⋙ dest P D :=
  (P.lift (Quiver.Hom.op v)).leftOp

abbrev Row (Y : Dual (B := B)) (A : B) := Grothendieck (dest P A ⋙ decode Y)

theorem exactDiagram (Y : Dual (B := B)) (A : B) :
    dest P A ⋙ decode Y = diagram Y (P.extend (op A)) := rfl

/-- Two chart opposites cancel before the native covariant grade/body is read. -/
def rowIso (Y : Dual (B := B)) (A : B) :
    CategoryTheory.IsoCat ((Total Y (P.extend (op A)))ᵒᵖ) (Row P Y A) where
  functor := unopUnop _
  inverse := opOp _
  unit_eq := rfl
  counit_eq := rfl

def pair (Y : Dual (B := B)) {A : B} (q : (grades P).obj A)
    (y : (decode Y).obj ((dest P A).obj q)) : Row P Y A := ⟨q,y⟩

def arrow {Y : Dual (B := B)} {A : B} {x z : Row P Y A} (s : x.base ⟶ z.base)
    (v : ((decode Y).map ((dest P A).map s)).toFunctor.obj x.fiber ⟶ z.fiber) :
    x ⟶ z := ⟨s,v⟩

theorem readGrade {Y : Dual (B := B)} {A : B}
    {x z : (Total Y (P.extend (op A)))ᵒᵖ} (f : x ⟶ z) :
    ((rowIso P Y A).functor.map f).base = (gradeMap f.unop).op := rfl

theorem readPayload {Y : Dual (B := B)} {A : B}
    {x z : (Total Y (P.extend (op A)))ᵒᵖ} (f : x ⟶ z) :
    ((rowIso P Y A).functor.map f).fiber = (payloadMap f.unop).op := rfl

/-- Covariant reindexing uses the cocartesian comparison as given, not its inverse. -/
def restrict (Y : Dual (B := B)) {A D : B} (v : A ⟶ D) : Row P Y A ⥤ Row P Y D :=
  (rowIso P Y A).inverse ⋙ (P.baseRestrict Y v.op).op ⋙ (rowIso P Y D).functor

theorem restrictPair (Y : Dual (B := B)) {A D : B} (v : A ⟶ D)
    (q : (grades P).obj A) (y : (decode Y).obj ((dest P A).obj q)) :
    (restrict P Y v).obj (pair P Y q y) =
      pair P Y (((grades P).map v).toFunctor.obj q) (((decode Y).map ((lift P v).app q)).toFunctor.obj y) := rfl

theorem restrictGrade {Y : Dual (B := B)} {A D : B} (v : A ⟶ D)
    {x z : Row P Y A} (h : x ⟶ z) :
    ((restrict P Y v).map h).base = ((grades P).map v).toFunctor.map h.base := rfl

end ContextualComposition.GrothendieckStep.ContentCovariantGrothendieck
