import ContextualComposition.ContextadStrictRoutes
import ContextualComposition.ContextadFinal
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage
namespace SwitchProbe
noncomputable section
inductive Shade | white | black deriving DecidableEq
instance : Groupoid Shade where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  inv _ := ()
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Shade)
  extend a := (Functor.const _).obj a
  lift f := { app := fun _ => f }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
abbrev src := (power S 2).source
def color (n : Nat) := if n=0 then Shade.white else Shade.black
def tensor : (power S 2).apex ⥤ Apex P where
  obj x := pair _ _ (src.obj x) (color (src.obj x))
  map f := arrow (src.map f) ()
  map_id _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
  map_comp _ _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
def m : ContextadTotal.Native S where
  grade := tensor
  over := rfl
  delta := { app := fun _ => 𝟙 _ }
  cart {x y} f _ := by
    let k : color (src.obj x) ⟶ color (src.obj y) := ()
    have : IsIso (payloadMap (tensor.map f)) := (inferInstance : IsIso k)
    exact ContextadCartesian.cart_of_payload _ _ (tensor.map f)
def Y : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Unit))
def input (n : Nat) : Total Y (power S 2).dest :=
  pair _ _ (pair _ _ (pair _ _ n Shade.white) Shade.white) (Discrete.mk ())
abbrev a : (0:Nat) ⟶ 1 := homOfLE (by decide)
def z : (PackedFree.pow S Y 2).obj (op 1) := payload _ _ ((BlockEvaluation.global S Y 2).obj (input 1))
/-- Move a real two-grade input across a nonidentity base arrow, then apply the native
tensor, versus pull back its output. The cartesian comparison can relate distinct objects. -/
abbrev x := grade _ _ (input 1)
abbrev chosen := NativeCleavage.powerChoice S 1 0 x a
abbrev other := NativeCleavage.powerChoice S 0 0 (tensor.obj x) a
example : Cartesian (power S 1).source (tensor.map chosen.lift) := m.cart _ chosen.cart
example : payload _ _ (tensor.obj chosen.obj) = Shade.white := rfl
example : payload _ _ other.obj = Shade.black := rfl
example : tensor.obj chosen.obj ≠ other.obj := by intro h; cases (congrArg (fun w : Apex P => payload _ _ w) h)
abbrev H (n : Nat) := PackedFree.pow S Y n
abbrev tag (x : Total (H 1) (𝟭 Nat)) : Shade := grade _ _ (payload _ _ x)
theorem allColor (w : Total Y (power S 2).dest) :
    tag ((BlockEvaluation.global S Y 1).obj ((ContextadTotal.action m Y).obj w)) =
      color (src.obj (grade _ _ w)) := by
  have h := SpanPayload.total_projection Y (powerComparison S 0) _ (comparison_dest S 0)
  have e := Functor.congr_obj h ((ContextadTotal.action m Y).obj w)
  exact congrArg (fun g : chainApex S 0 => match g.2 with | .cons p _ => p) e
theorem atBase (j : Nat) (z : (H 2).obj (op j)) :
    tag ((ContextadTotal.total m Y).obj ((FibreValue.incl (H 2) j).obj z)) = color j := by
  let w := (BlockEvaluation.global S Y 2).strictInv.obj ((FibreValue.incl (H 2) j).obj z)
  have h := Functor.congr_obj (BoundaryPaste.invOver _ _ _ (BlockEvaluation.globalOver S Y 2)) ((FibreValue.incl (H 2) j).obj z)
  exact (allColor w).trans (congrArg color h)
theorem localColor (j : Nat) (q : (H 2).obj (op j)) :
    grade _ _ ((ContextadTotal.binary m Y j).obj q) = color j :=
  (congrArg tag (Functor.congr_obj (ContextadRecognition.localIncl m j Y) q)).trans (atBase j q)
noncomputable abbrev nativeData := ContextadSpecialize.data m
theorem oldColor (j : Nat) (q : (H 2).obj (op j)) :
    grade _ _ ((ContextadTensor.binary nativeData Y j).obj q) = color j :=
  (congrArg (grade Y (P.extend j)) (Functor.congr_obj (ContextadFinal.identify m nativeData Y j (ContextadSpecialize.agrees m j)) q)).trans (localColor j q)
example : ((H 2).map a.op).toFunctor ⋙ ContextadTensor.binary nativeData Y 0 ≅
    ContextadTensor.binary nativeData Y 1 ⋙ P.baseRestrict Y a := ContextadFinal.nativeExterior m Y a
theorem notStrict : ¬ (((H 2).map a.op).toFunctor ⋙ ContextadTensor.binary nativeData Y 0 =
    ContextadTensor.binary nativeData Y 1 ⋙ P.baseRestrict Y a) := by
  intro h
  have e := congrArg (grade Y (P.extend 0)) (Functor.congr_obj h z)
  change grade _ _ ((ContextadTensor.binary nativeData Y 0).obj (((H 2).map a.op).toFunctor.obj z)) =
    grade _ _ ((ContextadTensor.binary nativeData Y 1).obj z) at e
  rw [oldColor,oldColor] at e
  cases e
end
end SwitchProbe

namespace IndependentWeakNotStrict
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage FibreValue ContextadLawTransport ContextadNativeLaws SwitchProbe
noncomputable section
set_option backward.isDefEq.respectTransparency false
theorem uniqueApex {x y : Apex P} (f g : x ⟶ y) : f = g := by
  apply (homEquiv _ _).injective
  exact Sigma.ext (Subsingleton.elim _ _) (HEq.rfl : HEq () ())
def d : ContextadUnit.Data P where
  grade _ := Shade.white
  discharge _ := 𝟙 _
  reindex _ := rfl
  square _ := Subsingleton.elim _ _
def verticalIso {x y : Apex P} (h : (left P).obj x = (left P).obj y) : x ≅ y where
  hom := arrow (eqToHom h) ()
  inv := arrow (eqToHom h.symm) ()
  hom_inv_id := uniqueApex _ _
  inv_hom_id := uniqueApex _ _
theorem overEq {n : Nat} (r s : ContextadRoutes.Map S n 1) (x : (power S n).apex) :
    (left P).obj (r.grade.obj x) = (left P).obj (s.grade.obj x) :=
  (Functor.congr_obj r.over x).trans (Functor.congr_obj s.over x).symm
def cell {n : Nat} (r s : ContextadRoutes.Map S n 1) : Cell r s where
  grade := NatIso.ofComponents (fun x => verticalIso (overEq r s x)) (fun _ => uniqueApex _ _)
  source x := ⟨overEq r s x, Subsingleton.elim _ _⟩
  endpoint := NatTrans.ext (funext fun _ => Subsingleton.elim _ _)
def allConstraints : Constraints d m := ⟨cell _ _,cell _ _,cell _ _⟩
example := leftUnitor d m Y 1 allConstraints
example := rightUnitor d m Y 1 allConstraints
example := ContextadNativeLaws.associator d m Y 1 allConstraints
theorem noStrictLeft (J : (H 1).obj (op 1) ⥤ (H 2).obj (op 1)) :
    J ⋙ ContextadCoherence.actual m Y 1 ≠ 𝟭 _ := by
  intro e
  let w : (H 1).obj (op 1) := pair _ _ Shade.white (Discrete.mk ())
  have h := congrArg (grade Y (P.extend 1)) (Functor.congr_obj e w)
  change grade _ _ ((ContextadTensor.binary nativeData Y 1).obj (J.obj w)) = Shade.white at h
  rw [oldColor] at h
  cases h
theorem noStrictData : ¬ ContextadStrictRoutes.StrictData d m :=
  fun e => noStrictLeft _ (ContextadStrictRoutes.left d m e Y 1)
end
end IndependentWeakNotStrict
#print axioms IndependentWeakNotStrict.allConstraints
#print axioms IndependentWeakNotStrict.noStrictLeft
#print axioms IndependentWeakNotStrict.noStrictData
