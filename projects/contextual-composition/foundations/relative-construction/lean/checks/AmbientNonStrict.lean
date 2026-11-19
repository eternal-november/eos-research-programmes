import ContextualComposition.ContextadAmbientLift
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks
namespace CentralProbe
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
end CentralProbe
