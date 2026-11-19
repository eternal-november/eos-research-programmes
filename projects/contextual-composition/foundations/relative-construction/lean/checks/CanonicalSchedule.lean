import ContextualComposition.ContextadPentagonSchedule
import ContextualComposition.ContextadScheduleDetection
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
open ContextadSchedule ContextadHorizontalLaws
theorem thinCoherent : Coherent d m allConstraints :=
  ⟨fun _ => uniqueApex _ _,fun _ => uniqueApex _ _⟩
example (Y : PackedCuts.Psh.{0,0,0,0} Nat) := triangleBase d m allConstraints thinCoherent.triangle Y
example (Y : PackedCuts.Psh.{0,0,0,0} Nat) := pentagonBase d m allConstraints thinCoherent.pentagon Y
example := ContextadScheduleDetection.pathIff
  (pentLong d m allConstraints (canonicalPentagon d m allConstraints))
  (pentShort d m allConstraints (canonicalPentagon d m allConstraints))
end
end IndependentWeakNotStrict
