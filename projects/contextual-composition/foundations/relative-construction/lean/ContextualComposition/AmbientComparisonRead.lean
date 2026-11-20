module
public import ContextualComposition.AmbientCoordinates
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientComparisonRead
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientRoundTrip AmbientCellFunctor AmbientWhiskering AmbientCellTrace AmbientBlockIteration
open AmbientBicategory AmbientCoordinates ContextadLawTransport ContextadModification NativeBlocks WordTrace CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
local instance instHom {L : Type*} [Bicategory L] {M : Type*} [Bicategory M] (F G : Pseudofunctor L M) : Category (StrongTrans F G) := StrongTrans.homCategory
universe u v
section Generic
variable {B : Type u} [Category.{v} B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u}) {F G : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)}
variable (f : F ⋙ proj Z = proj Y) (g : G ⋙ proj Z = proj Y) (c : F ≅ G) (z : ∀ x, Pure ((proj Z).map (c.hom.app x)))
variable (p : Pres F (proj Y) (proj Z)) (q : Pres G (proj Y) (proj Z))
theorem isoModAt (x) : Aligned ((totalCell (invertibleMod Y Z F G f g c z p q).hom.as).app x) (c.hom.app x) := by
  rw [totalApp]
  let A := grade _ _ x
  let k := (onFiber F G f g c z A).hom.app ((embed Y A).obj (payload _ _ x))
  exact ((NativeCube.functorAlign (value_embed Z A) k).map Fiber.fiberInclusion).trans (fibreAligned F G f g c z A _)
theorem frameInv {a b c d : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} (h : a = b) (k : c = d) (s : ModIso c b) (x) :
    ev ((eqToIso h ≪≫ s.symm ≪≫ eqToIso k).inv) x = ev s.hom x := by subst b; subst d; simp
end Generic
theorem chartConj {C D E T : Type*} [Category* C] [Category* D] [Category* E] [Category* T]
    (U : C ⥤ D) (V : E ⥤ T) [U.IsIso] [V.IsIso] {F G : C ⥤ E} (t : F ⟶ G) (x) :
    Aligned (V.strictInv.map (V.map (t.app (U.strictInv.obj (U.obj x))))) (t.app x) :=
  (NativeCube.functorAlign V.asIsomorphism.unit_eq.symm _).trans (ContextadPayloadModification.appChange t (Functor.congr_obj U.asIsomorphism.unit_eq.symm x))
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {X Y : Obj.{u,v} B} {i j : Nat}
theorem modAt {f g : X ⟶ Y} (t : f ⟶ g) (n : Nat) (x) :
    Aligned (atRaw S (cell S n t) x) ((endpointCell (power S n).dest t.hom.as).app x) := by
  let U := chart S X n
  let V := chart S Y n
  let w := U.obj x
  have a := alignEdge (AmbientCellTrace.decoded _ _ (blockOver S f.hom n) (blockOver S g.hom n) (blockCell S t.hom.as n) (blockVertical S t.hom.as n) (blockPres S f.hom n) (blockPres S g.hom n) w)
  exact (a.map V.strictInv).trans (chartConj U V (endpointCell _ t.hom.as) x)
variable (r : ContextadRoutes.Map S i j) (p : gradeCart r) (f : X ⟶ Y)
noncomputable abbrev q := AmbientMateCalculus.q (power S i).dest (power S j).dest r.grade r.leg f.hom
theorem comparisonAt (x) :
    Aligned (atRaw S (comparison S r p f).inv x) ((q S r f).app x) := by
  let U := chart S X i
  let V := chart S Y j
  let z := U.obj x
  let a := f.hom
  have ef := frameInv (PackedFree.pow S (underlying X) i) (PackedFree.pow S (underlying Y) j)
    (AmbientOperationBoundaries.descendComp _ _ _ (blockOver S a i) (over (underlying Y) r) (blockPres S a i) (globalPres (underlying Y) r p) (rightOver a r))
    (AmbientOperationBoundaries.descendComp _ _ _ (over (underlying X) r) (blockOver S a j) (globalPres (underlying X) r p) (blockPres S a j) (leftOver a r)).symm
    (weakOperationIso a r p) z
  have v := isoModAt _ _ (leftOver a r) (rightOver a r) (operationSquare a r) (operationBase a r)
    (fun z k => blockPres S a j _ (globalPres (underlying X) r p z k)) (fun z k => globalPres (underlying Y) r p _ (blockPres S a i z k)) z
  have w : Aligned ((operationSquare a r).hom.app z) (V.map ((q S r f).app (U.strictInv.obj z))) :=
    AmbientDescentRecognition.trim _ _ _ ⟨_,eqToHom_app (toLeft a r) z⟩ ⟨_,eqToHom_app (toRight a r).symm z⟩
  exact ((((alignEdge ef).trans v).trans w).map V.strictInv).trans (chartConj U V _ x)
end ContextualComposition.GrothendieckStep.AmbientComparisonRead
