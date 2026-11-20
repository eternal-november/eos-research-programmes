import ContextualComposition.RepresentableKleisliData
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

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open ContextualComposition.GrothendieckStep AmbientBicategory RepresentableKleisli
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
namespace StrongYonedaNotStrict
set_option backward.isDefEq.respectTransparency false
open SwitchProbe IndependentWeakNotStrict
noncomputable def coherentData : AmbientCoherentPseudomonad.Data S :=
  AmbientCoherentPseudomonad.build d m allConstraints thinCoherent
abbrev Y := AmbientBicategory.underlying (KObj S 1)
def point (J : Nat) (a : Shade) (w : J ⟶ (1:Nat)) : Y.obj (op J) :=
  pair (RepresentableYoneda.rep 1) (P.extend J) a (Discrete.mk w)
theorem thin (J : Nat) {x y : Y.obj (op J)} (f g : x ⟶ y) : f = g :=
  RepresentableComma.arrowExt (P.extend J) 1 f g (@Subsingleton.elim Unit inferInstance (gradeMap f) (gradeMap g))
def any (J : Nat) (x y : Y.obj (op J)) : x ⟶ y :=
  arrow (show grade _ (P.extend J) x ⟶ grade _ (P.extend J) y from ()) (eqToHom (by
    apply Discrete.ext; exact @Subsingleton.elim (J ⟶ (1:Nat)) inferInstance _ _))
def changeShade (J : Nat) (x y : Y.obj (op J)) : x ≅ y where
  hom := any J x y
  inv := any J y x
  hom_inv_id := thin J _ _
  inv_hom_id := thin J _ _
def F (c : Shade) (J : Nat) : (RepresentableYoneda.rep (1:Nat)).obj (op J) ⥤ Y.obj (op J) :=
  Discrete.functor fun w => point J (if J=0 then c else Shade.white) w
def strong (c : Shade) : RepresentableYoneda.Hom Y 1 :=
  ContextadStrong.assemble (G := RepresentableYoneda.rep 1) (H := Y) (F c)
    (fun {_D J} _ => NatIso.ofComponents (fun _ => changeShade J _ _) (fun _ => thin J _ _))
    (fun J _ => thin J _ _)
    (fun {A _D _E} _ _ _ => thin A _ _)
def kle (c : Shade) : KH S 1 1 := CategoryTheory.Bicategory.InducedBicategory.mkHom (strong c)
theorem sameRow : row (kle Shade.white) = row (kle Shade.black) := rfl
theorem different : kle Shade.white ≠ kle Shade.black := by
  intro h
  have r := congrArg (fun k : KH S 1 1 =>
    grade (RepresentableYoneda.rep 1) (P.extend 0)
      (RepresentableYoneda.atPoint Y 1 k.hom (homOfLE (by decide : (0:Nat) ≤ 1)))) h
  change Shade.white = Shade.black at r
  cases r
theorem noLiteralInverse : ¬ Function.Injective (row (S := S) (A := 1) (D := 1)) :=
  fun h => different (h sameRow)
end StrongYonedaNotStrict
#print axioms StrongYonedaNotStrict.noLiteralInverse
