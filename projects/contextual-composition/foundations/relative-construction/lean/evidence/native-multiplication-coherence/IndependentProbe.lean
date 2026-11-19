import ContextualComposition.ContextadNativeLaws
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage TelescopeSquares SpanPayload.Power
namespace MovingMixed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend _ := 𝟭 Nat
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
abbrev src := (power S 2).source
def tensor : (power S 2).apex ⥤ Apex P where
  obj x := pair _ _ (src.obj x) (0 : Nat)
  map f := arrow (src.map f) (𝟙 (0 : Nat))
  map_id _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
  map_comp _ _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
def m : ContextadTotal.Native S where
  grade := tensor
  over := rfl
  delta := { app := fun x => homOfLE (Nat.zero_le _) }
  cart {x y} f _ := by
    have : IsIso (payloadMap (tensor.map f)) := (inferInstance : IsIso (𝟙 (0:Nat)))
    exact ContextadCartesian.cart_of_payload _ _ (tensor.map f)
def gradeRow (a p r : Nat) : (power S 2).apex := pair _ _ (pair _ _ a p) r
example : ¬ IsIso (m.delta.app (gradeRow 4 1 3)) := by
  intro h; exact (by decide : ¬3 ≤ 0) (leOfHom (inv (m.delta.app (gradeRow 4 1 3))))
inductive W | pt
instance : Category W where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc _ _ _
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj a := Cat.of (Fin (a.unop+1) → W)
  map {a _} f := (Pi.comap (fun _ : Fin (a.unop+1) => W) (Fin.castLE (Nat.succ_le_succ f.unop.le))).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def input (a p r : Nat) : Total Y (power S 2).dest := pair _ _ (gradeRow a p r) (fun _ => W.pt)
def f (words : Fin 4 → List Nat) : input 4 1 3 ⟶ input 4 2 5 :=
  arrow (arrow (arrow (𝟙 (4:Nat)) (show (1:Nat) ⟶ 2 from homOfLE (by decide))) (show (3:Nat) ⟶ 5 from homOfLE (by decide))) words
theorem readWord (w : Fin 4 → List Nat) :
    payloadMap ((ContextadTotal.action m Y).map (f w)) (0 : Fin 1) = w 0 := by
  rw [restrict_payload]
  change w _ ++ [] = _
  exact List.append_nil _
/-- Exact kernel of weighting on these nonvertical grade edges. -/
theorem same_iff (w v : Fin 4 → List Nat) :
    (ContextadTotal.action m Y).map (f w) = (ContextadTotal.action m Y).map (f v) ↔ w 0 = v 0 := by
  constructor
  · intro h
    exact (readWord w).symm.trans ((congrArg (fun g : (ContextadTotal.action m Y).obj (input 4 1 3) ⟶
      (ContextadTotal.action m Y).obj (input 4 2 5) => payloadMap g (0 : Fin 1)) h).trans (readWord v))
  · intro h
    apply (homEquiv _ _).injective
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    funext i
    have hi : i = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance _ _
    subst i
    exact (readWord w).trans (h.trans (readWord v).symm)
def row (p r : Nat) : Fibre.asCat (Y := Y) S 2 4 :=
  ⟨.cons p (.cons r (.nil _)),fun _ => W.pt⟩
def moving (words : Fin 4 → List Nat) : row 1 3 ⟶ row 2 5 :=
  ⟨⟨(show (1:Nat) ⟶ 2 from homOfLE (by decide)),(show (3:Nat) ⟶ 5 from homOfLE (by decide)),PUnit.unit⟩, words⟩
abbrev a : (1:Nat) ⟶ 4 := homOfLE (by decide)
def actual (w : Fin 4 → List Nat) := (Fibre.comparison (Y := Y) S 2 4).map (moving w)
example (w : Fin 4 → List Nat) :=
  (ContextadFinal.nativeExterior m Y a).hom.naturality (actual w)
/-- Erasure to a terminal payload gives a genuinely different target presheaf. -/
def Z : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Unit))
def erase : Y ⟶ Z where
  app a := ((Functor.const (Y.obj a)).obj (Discrete.mk ())).toCatHom
  naturality _ _ _ := rfl
example := ContextadStrong.multiplication m Y
example : FinalCube.Mix.Diagram (ContextadMixed.actualMix m erase a) :=
  ContextadMixed.actualDiagram m erase a
end
end MovingMixed

namespace IndependentSurvivingPayload
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep MovingMixed
noncomputable section
def kept : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of W)
def read0 : Y ⟶ kept where
  app a := (Pi.eval (fun _ : Fin (a.unop+1) => W) 0).toCatHom
  naturality _ _ _ := rfl
example : FinalCube.Mix.Diagram (ContextadMixed.actualMix m read0 a) :=
  ContextadMixed.actualDiagram m read0 a
def w1 (i : Fin 4) : List Nat := [i.val]
def w2 (i : Fin 4) : List Nat := if i.val = 0 then [0] else []
example : (ContextadTotal.action m Y).map (f w1) = (ContextadTotal.action m Y).map (f w2) :=
  (same_iff ..).2 rfl
example : f w1 ≠ f w2 := by
  intro h
  have e := congrArg (fun z : input 4 1 3 ⟶ input 4 2 5 => payloadMap z (1 : Fin 4)) h
  change ([1] : List Nat) = [] at e
  cases e
example : ((read0.app (op 0)).toFunctor.map
    (payloadMap ((ContextadTotal.action m Y).map (f w1)))) = [0] := readWord w1
end
end IndependentSurvivingPayload
#print axioms IndependentSurvivingPayload.read0
#print axioms MovingMixed.same_iff
#print axioms ContextualComposition.GrothendieckStep.ContextadMixed.actualDiagram
