import ContextualComposition.AmbientSuffixFactor
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks
namespace SuffixSignedCone
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
open ContextadOuterCharts ContextadWeakAction ContextadAmbientPayload ContextadWeakWeight AmbientSuffixFactor FibreValue TelescopeSquares
abbrev D := 𝟭 Nat
abbrev E := (Functor.const Nat).obj (1:Nat)
abbrev W := (Functor.const Nat).obj (0:Nat)
abbrev R := 𝟭 Nat
def leg : R ⋙ W ⟶ E := { app _ := homOfLE (by decide : 0 ≤ 1) }
def row : Total G (E ⋙ D) := pair _ _ 3 O.pt
noncomputable abbrev sq := square alpha D E W R leg
noncomputable abbrev Q := sq.app row
noncomputable abbrev out := (atEndpoint alpha D).map ((liftTail G D R leg).app row)
theorem fixed : Aligned ((pull D G W).map Q ≫ (liftTail G D R leg).app ((atEndpoint alpha (E ⋙ D)).obj row)) out :=
  natural alpha D E W R leg row
theorem gradeOnly : Pure (gradeMap Q) := weakGrade _ _ _ _ alpha row
noncomputable abbrev reference := (totalStrong alpha).map ((tip G (E ⋙ D) (W ⋙ D) R (whiskerRight leg D)).app row)
theorem outBit : (payloadMap reference : Bool) = true := rfl
theorem referenceNotPure : ¬ Pure (payloadMap reference) := by
  rintro ⟨e,h⟩
  have t : (eqToHom e : O.pt ⟶ O.pt) = false := rfl
  cases outBit.symm.trans (h.trans t)
theorem outNotPure : ¬ Pure (payloadMap out) := by
  intro p
  have a := NativeCube.functorAlign (actionLeaf D (totalStrong alpha) (strongOver alpha)) ((liftTail G D R leg).app row)
  exact referenceNotPure (ContextadOuterRigidity.payloadAligned (Y := G) (e := 𝟭 Nat) a.symm p)
theorem notTransport : ¬ Pure Q := by
  intro h
  let t := (liftTail G D R leg).app ((atEndpoint alpha (E ⋙ D)).obj row)
  have k := (trimHead ((pull D G W).map Q) t (pureMap (pull D G W) h)).symm.trans fixed
  exact outNotPure (ContextadOuterRigidity.payloadAligned (Y := G) (e := D) k.symm (pureId _))
theorem noReverse : ¬ IsIso (leg.app 3) := by
  intro h; obtain ⟨j,_,_⟩ := h.out; exact (by decide : ¬1 ≤ 0) (leOfHom j)
end
end SuffixSignedCone
#print axioms SuffixSignedCone.notTransport
#print axioms SuffixSignedCone.fixed
