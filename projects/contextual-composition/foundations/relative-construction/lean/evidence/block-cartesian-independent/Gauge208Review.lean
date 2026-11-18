import ContextualComposition.BlockCartesian
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeCleavage BlockCartesian
namespace GaugeReview
set_option backward.isDefEq.respectTransparency false
inductive G | pt
instance : Category G where
  Hom _ _ := Int
  id _ := 0
  comp f g := f + g
  id_comp := by intros; apply Int.zero_add
  comp_id := by intros; apply Int.add_zero
  assoc := by intros; apply Int.add_assoc
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of G)
  extend a := (Functor.const _).obj a
  lift f := { app := fun _ => f }
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
abbrev p := (power S 1).source
def cellRead : (power S 1).apex ⥤ G where
  obj x := payload P.grades (𝟭 Nat) x
  map h := payloadMap h
  map_id _ := rfl
  map_comp a b := (payload_comp a b).trans (congrArg (fun n : Int => (show Int from payloadMap a) + n) (Int.add_zero (payloadMap b)))
def q (A : Nat) (y : (power S 1).apex) := pair P.grades (𝟭 Nat) A (payload P.grades (𝟭 Nat) y)
def m (A : Nat) (y : (power S 1).apex) (a : A ⟶ p.obj y) (k : Int) : q A y ⟶ y := arrow a k
theorem mCart (A : Nat) (y : (power S 1).apex) (a : A ⟶ p.obj y) (k : Int) :
    Cartesian p (m A y a k) := by
  intro z g b _
  let h : z ⟶ q A y := arrow b ((show Int from payloadMap g) - k)
  refine ⟨h,⟨rfl,?_⟩,?_⟩
  · apply (homEquiv _ _).injective
    apply Sigma.ext (Subsingleton.elim _ _)
    apply heq_of_eq
    change cellRead.map (h ≫ m A y a k) = cellRead.map g
    rw [cellRead.map_comp]
    change ((show Int from payloadMap g) - k) + k = (show Int from payloadMap g)
    omega
  · intro u hu
    apply (homEquiv _ _).injective
    apply Sigma.ext (Subsingleton.elim _ _)
    apply heq_of_eq
    have w := congrArg cellRead.map hu.2
    rw [cellRead.map_comp] at w
    change (show Int from payloadMap u) + k = (show Int from payloadMap g) at w
    change (show Int from payloadMap u) = (show Int from payloadMap g) - k
    omega
def choices (k : Nat → Nat → Int) : (n : Nat) → Cleavage (power S n).source
  | 0 => baseChoice
  | 1 => fun A y a => ⟨q A y,rfl,m A y a (k A (p.obj y)),Subsingleton.elim _ _,mCart A y a (k A (p.obj y))⟩
  | n+2 => SpanPull.All.parts S (n+2)
def gauge (k : Nat → Nat → Int) := SpanPull.choice _ (choices k)
def JL := gauge (fun A D => (A:Int)*D + 1)
def JR := gauge (fun A D => (D:Int)-(A:Int)+2)
def L := All.nestedChoice S JL
def readPart : (n : Nat) → (power S n).apex ⥤ G
  | 1 => cellRead
  | _ => (Functor.const _).obj G.pt
def read := Sigma.desc readPart
def value {x y : G} (f : x ⟶ y) : Int := f
theorem alignedValue {x y x' y' : G} {f : x ⟶ y} {g : x' ⟶ y'} (a : TelescopeSquares.Aligned f g) :
  value f = value g := by obtain ⟨h,h',j⟩ := a; subst x'; subst y'; exact congrArg value (by simpa using j : f = g)
def x (A : Nat) := pair P.grades (𝟭 Nat) A G.pt
def z (A : Nat) : (All.source S).Fiber A := ⟨⟨1,⟨1,x A⟩⟩,rfl⟩
def obs (A : Nat) : (leftLeg S).Fiber A := ⟨⟨1,x A⟩,rfl⟩
noncomputable abbrev F (A : Nat) := SpanPayload.fibreFunctor (flatten S) (leftLeg S) (flatten_source S) A
theorem obsEq (A : Nat) : (F A).obj (z A) = obs A :=
  Subtype.ext (Functor.congr_obj (SpanPayload.fibre_diagram (flatten S) (leftLeg S) (flatten_source S) A) (z A))
noncomputable abbrev face {A D : Nat} (a : A ⟶ D) := All.sourceFace S L JR a
/-- A uniform calculation for all lengths of the base interval, including identities. -/
theorem cost {A D : Nat} (a : A ⟶ D) :
  value (read.map ((face a).sq.hom.app (z D)).val) = ((A:Int)*D + 1) - ((D:Int)-A+2) := by
  have w := alignedValue (((face a).fac (z D)).map read)
  rw [read.map_comp] at w
  change value (read.map ((face a).sq.hom.app (z D)).val) + value (read.map (Reindex.lift JR a ((F D).obj (z D)))) = (A:Int)*D+1 at w
  rw [obsEq] at w
  change _ + ((D:Int)-A+2) = (A:Int)*D+1 at w
  omega
example : value (read.map ((face (homOfLE (show 2 ≤ 5 by decide))).sq.hom.app (z 5)).val) = 6 := by rw [cost]; decide
example : value (read.map ((face (𝟙 (5:Nat))).sq.hom.app (z 5)).val) = 24 := by rw [cost]; decide
example : value (read.map ((face (homOfLE (show 5 ≤ 7 by decide))).sq.hom.app (z 7)).val) = 32 := by rw [cost]; decide
example : value (read.map ((face (homOfLE (show 2 ≤ 7 by decide))).sq.hom.app (z 7)).val) = 8 := by rw [cost]; decide
end GaugeReview
