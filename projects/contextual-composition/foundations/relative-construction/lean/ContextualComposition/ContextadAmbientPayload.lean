module
public import ContextualComposition.ContextadOuterRigidity
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadAmbientPayload
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
universe u v
variable {B : Type*} [Category* B] (Y : Bᵒᵖ ⥤ Cat.{v,u})
abbrev Co := Pseudofunctor.CoGrothendieck Y.toPseudofunctor'
def readObj (x : Total Y (𝟭 B)) : Co Y := ⟨grade Y _ x,payload Y _ x⟩
def writeObj (x : Co Y) : Total Y (𝟭 B) := pair _ _ x.base x.fiber
def readArrow {x y : Total Y (𝟭 B)} (f : x ⟶ y) : readObj Y x ⟶ readObj Y y :=
  ⟨gradeMap f,payloadMap f⟩
def writeArrow {x y : Co Y} (f : x ⟶ y) : writeObj Y x ⟶ writeObj Y y := arrow f.base f.fiber
theorem readWrite (x : Co Y) : readObj Y (writeObj Y x) = x := rfl
theorem writeRead (x : Total Y (𝟭 B)) : writeObj Y (readObj Y x) = x := rfl
theorem readId (x : Total Y (𝟭 B)) : readArrow Y (𝟙 x) = 𝟙 (readObj Y x) := by
  apply CoGrothendieck.Hom.ext (readArrow Y (𝟙 x)) (𝟙 (readObj Y x)) rfl
  change payloadMap (𝟙 x) = _ 
  simp only [CoGrothendieck.categoryStruct_id_fiber,Functor.toPseudofunctor'_mapId,eqToIso.inv,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app,eqToHom_refl,Category.comp_id]
  apply pureEq (WeightedCells.totalPureId Y (𝟭 B) x)
  exact ⟨_,rfl⟩
theorem readComp {x y z : Total Y (𝟭 B)} (f : x ⟶ y) (g : y ⟶ z) :
    readArrow Y (f ≫ g) = readArrow Y f ≫ readArrow Y g := by
  apply CoGrothendieck.Hom.ext (readArrow Y (f ≫ g)) (readArrow Y f ≫ readArrow Y g) rfl
  change payloadMap (f ≫ g) = _ 
  rw [payload_comp]
  simp only [CoGrothendieck.categoryStruct_comp_fiber,Functor.toPseudofunctor'_mapComp,eqToIso.inv,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app,eqToHom_refl,Category.comp_id]
  rfl
def read : Total Y (𝟭 B) ⥤ Co Y where
  obj := readObj Y
  map := readArrow Y
  map_id := readId Y
  map_comp := readComp Y
def write : Co Y ⥤ Total Y (𝟭 B) where
  obj := writeObj Y
  map := writeArrow Y
  map_id x := congrArg (writeArrow Y) (readId Y (writeObj Y x)).symm
  map_comp f g := congrArg (writeArrow Y) (readComp Y (writeArrow Y f) (writeArrow Y g)).symm
end ContextualComposition.GrothendieckStep.ContextadAmbientPayload
