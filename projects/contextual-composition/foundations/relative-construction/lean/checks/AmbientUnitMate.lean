import ContextualComposition.AmbientMonadMaps
import ContextualComposition.ContextadAmbientLift
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks
namespace AmbientUnitProbe
noncomputable section
set_option backward.isDefEq.respectTransparency false
inductive O | pt
instance : Groupoid O where
  Hom _ _ := Bool
  id _ := false
  comp a b := xor a b
  inv a := a
  id_comp := by intro _ _ f; cases f <;> rfl
  comp_id := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl
  inv_comp := by intro _ _ f; cases f <;> rfl
  comp_inv := by intro _ _ f; cases f <;> rfl
def G : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of O)
def shade (n : Nat) := decide (n=0)
def sign (x : O) (t : Bool) : x ≅ x where
  hom := t
  inv := t
  hom_inv_id := by cases t <;> rfl
  inv_hom_id := by cases t <;> rfl
def twistAt (i j : Nat) : 𝟭 O ≅ 𝟭 O := NatIso.ofComponents (fun x => sign x (xor (shade i) (shade j)))
  (fun {x y} f => by change xor f _ = xor _ f; cases shade i <;> cases shade j <;> cases f <;> rfl)
def face {i j : Nat} (a : i ⟶ j) : (G.map a.op).toFunctor ⋙ 𝟭 O ≅ 𝟭 O ⋙ (G.map a.op).toFunctor := twistAt i j
def alpha : CategoryTheory.Pseudofunctor.StrongTrans G.toPseudofunctor' G.toPseudofunctor' :=
  ContextadStrong.assemble (G := G) (H := G) (fun _ => 𝟭 O) (fun a => face a)
    (fun i x => by simp only [eqToHom_app]; change xor (xor (shade i) (shade i)) false = false; cases shade i <;> rfl)
    (fun {i j k} a b x => by simp only [eqToHom_app]; change xor (xor (shade i) (shade k)) false = xor false (xor (xor (shade i) (shade j)) (xor (shade j) (shade k))); cases shade i <;> cases shade j <;> cases shade k <;> rfl)
def z : Total G (𝟭 Nat) := pair _ _ (1:Nat) O.pt
def leg : (0:Nat) ⟶ 1 := homOfLE (by decide)
def f := NativeCleavage.pullLift G (𝟭 Nat) z leg
example : (payloadMap ((ContextadAmbientPayload.totalStrong alpha).map f) : Bool) = true := rfl
theorem notPure : ¬ FibreValue.Pure (payloadMap ((ContextadAmbientPayload.totalStrong alpha).map f)) := by
  rintro ⟨t,h⟩
  have : (eqToHom t : O.pt ⟶ O.pt) = false := rfl
  change true = (eqToHom t : O.pt ⟶ O.pt) at h
  cases h.trans this
end
end AmbientUnitProbe

namespace AmbientUnitProbe
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks
open ContextadWeakWeight ContextadOuterCharts ContextadAmbientPayload TelescopeSquares ContextadWeakAction FibreValue BoundaryPaste
open AmbientBicategory AmbientCoordinates
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
def P : Endpoints.{0,0,0,0} Nat where
  grades := G
  extend _ := (Functor.const O).obj 0
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def d : ContextadUnit.Data P where
  grade _ := O.pt
  discharge i := homOfLE (Nat.zero_le i)
  reindex _ := rfl
  square _ := Subsingleton.elim _ _
abbrev r := ContextadNativeLaws.insert S d
abbrev x : Raw S (G : Obj.{0,0} Nat) 0 := z
abbrev Q : Obj.{0,0} Nat := G
abbrev a : Q ⟶ Q := CategoryTheory.Bicategory.InducedBicategory.mkHom alpha
def rd {a b : Total G (𝟭 Nat)} (f : a ⟶ b) : Bool := payloadMap f
theorem aligned {a b c d : Total G (𝟭 Nat)} {f : a ⟶ b} {g : c ⟶ d} (h : Aligned f g) : rd f = rd g := by
  obtain ⟨rfl,rfl,q⟩ := h; simp at q; rw [q]
theorem castZero {a b : O} (h : a=b) : (eqToHom h : a ⟶ b) = false := by cases h; rfl
theorem rdComp {a b c : Total G (𝟭 Nat)} (f : a ⟶ b) (g : b ⟶ c) : rd (f ≫ g) = xor (rd f) (rd g) := by
  unfold rd; rw [payload_comp,castZero (comp_target (Y := G) (e := 𝟭 Nat) (gradeMap f) (gradeMap g) (payload G _ c))]
  exact congrArg (xor (payloadMap f)) (Bool.xor_false _)
theorem rdCast {a b : Total G (𝟭 Nat)} (t : a=b) : rd (eqToHom t) = false := by
  cases t; exact (WeightedCells.totalPureId G (𝟭 Nat) _).choose_spec.trans (castZero _)
abbrev J := leafAt G (power S 1).dest
theorem U : ContextadModification.gradeCart r := ContextadOuterCharts.unitCart d
theorem bit : rd (J.map ((AmbientComparisonRead.q S r a).app x)) = true := by
  have h := aligned (AmbientMateCalculus.factor (power S 0).dest (power S 1).dest r.grade r.leg alpha x)
  rw [rdComp] at h
  have leftBit : rd ((totalStrong alpha).map ((tip G _ _ r.grade r.leg).app x)) = true := rfl
  have rightBit : rd ((tip G _ _ r.grade r.leg).app ((atEndpoint alpha (power S 0).dest).obj x)) = false := rfl
  rwa [rightBit,leftBit,Bool.xor_false] at h
theorem notCast : ¬ Pure (atRaw S ((AmbientPseudonaturality.operation S r U).naturality a).inv x) := by
  intro h
  have w : Pure ((AmbientComparisonRead.q S r a).app x) := AmbientMateCalculus.pureOfAligned (AmbientComparisonRead.comparisonAt S r U a x).symm h
  obtain ⟨e,k⟩ := pureMap J w
  exact Bool.false_ne_true ((rdCast e).symm.trans ((congrArg rd k).symm.trans bit))
end
end AmbientUnitProbe
