module
public import ContextualComposition.AmbientOperationBoundaries
public import ContextualComposition.AmbientMateCalculus
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCoordinates
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientRoundTrip AmbientCellFunctor AmbientWhiskering AmbientCellTrace AmbientBlockIteration
open AmbientBicategory ContextadLawTransport ContextadModification NativeBlocks WordTrace CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {X Y Z W : Obj.{u,v} B} {i j k : Nat}
abbrev Raw (Q : Obj.{u,v} B) (n : Nat) := Total (underlying Q) (power S n).dest
abbrev chart (Q : Obj.{u,v} B) (n : Nat) := BlockEvaluation.global S (underlying Q) n
noncomputable abbrev encode (f : obj S i X ⟶ obj S j Y) := chart S X i ⋙ totalStrong f.hom ⋙ (chart S Y j).strictInv
noncomputable def atRaw {f g : obj S i X ⟶ obj S j Y} (t : f ⟶ g) (x : Raw S X i) :=
  (chart S Y j).strictInv.map ((totalCell t.hom.as).app ((chart S X i).obj x))
theorem extRaw {f g : obj S i X ⟶ obj S j Y} {t s : f ⟶ g} (k : ∀ x, Aligned (atRaw S t x) (atRaw S s x)) : t = s := by
  apply InducedBicategory.hom₂_ext; apply StrongTrans.Hom.ext; apply cellExt; intro y
  have surj : Function.Surjective (chart S X i).obj := fun z => ⟨(chart S X i).strictInv.obj z,Functor.congr_obj (chart S X i).asIsomorphism.counit_eq z⟩
  obtain ⟨x,rfl⟩ := surj y
  exact congrArg edge ((chart S Y j).strictInv.map_injective (k x).eq)
theorem compAt {f g h : obj S i X ⟶ obj S j Y} (t : f ⟶ g) (s : g ⟶ h) (x) :
    atRaw S (t ≫ s) x = atRaw S t x ≫ atRaw S s x := by
  unfold atRaw
  change (chart S Y j).strictInv.map ((totalCell (t.hom.as.vcomp s.hom.as)).app _) = _
  rw [totalComp,NatTrans.comp_app,Functor.map_comp]
theorem castAt {f g : obj S i X ⟶ obj S j Y} (h : f = g) (x) : Pure (atRaw S (eqToHom h) x) := by
  subst g
  unfold atRaw
  change Pure ((chart S Y j).strictInv.map ((totalCell (StrongTrans.Modification.id f.hom)).app _))
  rw [totalId,NatTrans.id_app,Functor.map_id]; exact pureId _
theorem alignEdge {C : Type*} [Category* C] {a b c d : C} {f : a ⟶ b} {g : c ⟶ d} (h : edge f = edge g) : Aligned f g :=
  alignOf (congrArg Edge.src h) (congrArg Edge.dst h) (Edge.hom_heq h)
theorem postAt {f g : obj S i X ⟶ obj S j Y} (t : f ⟶ g) (h : obj S j Y ⟶ obj S k Z) (x) :
    Aligned (atRaw S (t ▷ h) x) ((encode S h).map (atRaw S t x)) := by
  let C := chart S Y j
  let D := chart S Z k
  let u := (totalCell t.hom.as).app ((chart S X i).obj x)
  have a := (alignEdge (evRight t.hom h.hom ((chart S X i).obj x))).map D.strictInv
  have b := NativeCube.functorAlign C.asIsomorphism.counit_eq u
  exact a.trans ((b.map (totalStrong h.hom ⋙ D.strictInv)).symm)
theorem preAt (f : obj S i X ⟶ obj S j Y) {g h : obj S j Y ⟶ obj S k Z} (t : g ⟶ h) (x) :
    Aligned (atRaw S (f ◁ t) x) (atRaw S t ((encode S f).obj x)) := by
  let C := chart S Y j
  let D := chart S Z k
  let z := (totalStrong f.hom).obj ((chart S X i).obj x)
  have a := (alignEdge (evLeft f.hom t.hom ((chart S X i).obj x))).map D.strictInv
  exact a.trans ((ContextadPayloadModification.appChange (totalCell t.hom.as) (Functor.congr_obj C.asIsomorphism.counit_eq.symm z)).map D.strictInv)
theorem erase {C D E T : Type*} [Category* C] [Category* D] [Category* E] [Category* T]
    (U : C ⥤ D) (V : E ⥤ T) [U.IsIso] [V.IsIso] (f : C ⥤ E) :
    U ⋙ (U.strictInv ⋙ f ⋙ V) ⋙ V.strictInv = f :=
  (congrArg (· ⋙ f ⋙ V ⋙ V.strictInv) U.asIsomorphism.unit_eq.symm).trans (congrArg (f ⋙ ·) V.asIsomorphism.unit_eq.symm)
theorem mapEncode (f : X ⟶ Y) (n : Nat) : encode S (AmbientBicategory.map S n f) = atEndpoint f.hom (power S n).dest := by
  unfold encode AmbientBicategory.map
  change chart S X n ⋙ totalStrong (blockStrong (S := S) f.hom n) ⋙ (chart S Y n).strictInv = _
  rw [encodedBlock]; exact erase _ _ _
variable (r : ContextadRoutes.Map S i j) (p : gradeCart r)
noncomputable abbrev oper (X : Obj.{u,v} B) : obj S i X ⟶ obj S j X := InducedBicategory.mkHom (nativeStrong (underlying X) r p)
theorem opEncode (X : Obj.{u,v} B) : encode S (oper S r p X) = raw (underlying X) r := by
  change chart S X i ⋙ totalStrong (nativeStrong (underlying X) r p) ⋙ (chart S X j).strictInv = _
  rw [show totalStrong (nativeStrong (underlying X) r p) = _ from encodeDecode _ _ _ _ (globalPres (underlying X) r p)]
  exact erase _ _ _
noncomputable abbrev comparison (f : X ⟶ Y) :
    AmbientBicategory.map S i f ≫ oper S r p Y ≅ oper S r p X ≫ AmbientBicategory.map S j f :=
  InducedBicategory.isoMk (AmbientOperationBoundaries.operationIso f.hom r p)
end ContextualComposition.GrothendieckStep.AmbientCoordinates
