import ContextualComposition.ContentComposition
import ContextualComposition.ContentPurePin
import ContextualComposition.RepresentablePurePins
import ContextualComposition.ContextadPentagonSchedule
import ContextualComposition.ContextadScheduleDetection
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage
namespace ContentFixture
noncomputable section
inductive Shade | white | black deriving DecidableEq
instance : Groupoid Shade where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  inv _ := ()
def P : Endpoints.{0,0,0,0} Natᵒᵖ where
  grades := (Functor.const _).obj (Cat.of Shade)
  extend a := (Functor.const _).obj a
  lift f := { app := fun _ => f }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
abbrev src := (power S 2).source
def color (n : Nat) := if n=0 then Shade.white else Shade.black
def tensor : (power S 2).apex ⥤ Apex P where
  obj x := pair _ _ (src.obj x) (color (src.obj x).unop)
  map f := arrow (src.map f) ()
  map_id _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
  map_comp _ _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
def m : ContextadTotal.Native S where
  grade := tensor
  over := rfl
  delta := { app := fun _ => 𝟙 _ }
  cart {x y} f _ := by
    let k : color (src.obj x).unop ⟶ color (src.obj y).unop := ()
    have : IsIso (payloadMap (tensor.map f)) := (inferInstance : IsIso k)
    exact ContextadCartesian.cart_of_payload _ _ (tensor.map f)
end
end ContentFixture
namespace ContentCoherenceFixture
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage FibreValue ContextadLawTransport ContextadNativeLaws ContentFixture
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
end
end ContentCoherenceFixture

namespace ContentCoherentNative
open ContentFixture ContentCoherenceFixture
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
open ContentComposition ContentRepresentable ContentActualBend
set_option backward.isDefEq.respectTransparency false
noncomputable section
def T := AmbientCoherentPseudomonad.build d m allConstraints thinCoherent
def step (n : Nat) (p : Shade) : ContentComma.Native P n (n+1) :=
  StructuredArrow.mk (Y := op p) (homOfLE (Nat.le_succ n))

theorem terminalGrade :
    ((nativeComp T).obj (step 0 Shade.white,step 1 Shade.white)).right = op Shade.black := by
  rw [nativeFormula]
  let c := chunk (S := S) (step 0 Shade.white) (step 1 Shade.white)
  let G := SpanPayload.Power.gradeFunctor S 1 (op (2 : Nat))
  let c₀ := G.strictInv.obj c
  have cg : G.obj c₀ = c := Functor.congr_obj G.asIsomorphism.counit_eq c
  have h := Functor.congr_obj (ContextadSpecialize.gradeSpec m (op (2 : Nat))) c₀
  let shade : Apex P → Shade := fun q => payload P.grades (𝟭 _) q
  have z := congrArg shade h
  change color ((src.obj c₀.val).unop) = (ContextadSpecialize.grade m (op (2 : Nat))).obj (G.obj c₀) at z
  have cz : src.obj c₀.val = op (2 : Nat) := c₀.property
  rw [cg,cz] at z
  exact congrArg Opposite.op z.symm

theorem noReversedBody : ¬ Nonempty ((2 : Nat) ⟶ 0) :=
  fun ⟨a⟩ => (by decide : ¬ (2:Nat) ≤ 0) (leOfHom a)

theorem decodedPure : (localEquivalence T (contentAt (0 : Nat)) (contentAt (1 : Nat))).functor.obj
    (pureArrow T (homOfLE (by decide : (0:Nat) ≤ 1))) =
    StructuredArrow.mk (Y := op Shade.white) (homOfLE (by decide : (0:Nat) ≤ 1)) := by
  rw [readPure]
  rfl

def leg (n : Nat) : n ⟶ n+1 := homOfLE (Nat.le_succ n)

set_option linter.defProp false in
def originalPureComparator := RepresentablePurePins.binaryChart T (leg 1).op (leg 0).op

def actualContextBend :=
  RepresentablePurePins.bent T (leg 1).op (leg 0).op
    (RepresentableKleisli.pureK T (leg 1).op) (RepresentableKleisli.pureK T (leg 0).op)


end
end ContentCoherentNative
#print axioms ContentCoherentNative.terminalGrade
#print axioms ContentCoherentNative.decodedPure
#print axioms ContentCoherentNative.originalPureComparator
#print axioms ContentCoherentNative.actualContextBend
