import ContextualComposition.CutCompositor
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeCleavage BlockCartesian
namespace Gauge211
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
def Y := P.grades
def gauge (k : Int) : Cleavage (FibreValue.proj Y) := fun A y a =>
  ⟨q A y,rfl,m A y a k,Subsingleton.elim _ _,mCart A y a k⟩
def V := NativePacked.fixed S (0,0)
def L := extendChoice Y V.dest V.source (productChoice (𝟭 Nat) (𝟭 Nat) (𝟭 Nat) baseChoice baseChoice)
def pt (a : Nat) : (FibreTotal.projection Y V.dest V.source).Fiber a :=
  ⟨pair Y V.dest ⟨a,a,rfl⟩ G.pt,rfl⟩
def value {x y : G} (f : x ⟶ y) : Int := f
theorem alignedValue {x y x' y' : G} {f : x ⟶ y} {g : x' ⟶ y'} (a : TelescopeSquares.Aligned f g) :
  value f = value g := by obtain ⟨h,h',j⟩ := a; subst x'; subst y'; exact congrArg value (by simpa using j : f = g)
open BlockEvaluation
noncomputable abbrev face (k : Int) {a d : Nat} (u : a ⟶ d) := baseFace S Y 0 0 L (gauge k) u
noncomputable def label (k : Int) {a d : Nat} (u : a ⟶ d) := value (cellRead.map ((face k u).sq.hom.app (pt d)).val)
theorem readFace (k : Int) {a d : Nat} (u : a ⟶ d) :
    label k u + k = value (cellRead.map ((totalStages S Y 0 0).map (Reindex.lift L u (pt d)))) := by
  have e := alignedValue (((face k u).fac (pt d)).map cellRead)
  rw [cellRead.map_comp] at e
  exact e
-- The two independently chosen terminal gauges give distinct isomorphisms
-- even for the base identity; normalizing both identity faces would be false.
theorem difference {a d : Nat} (u : a ⟶ d) : label 2 u - label 5 u = 3 := by
  have t := (readFace 2 u).trans (readFace 5 u).symm
  omega
example : label 2 (𝟙 (3:Nat)) ≠ label 5 (𝟙 (3:Nat)) := by have t := difference (𝟙 (3:Nat)); omega
example : label 2 (homOfLE (show 2 ≤ 7 by decide)) - label 5 (homOfLE (show 2 ≤ 7 by decide)) = 3 := difference _
#check baseUnit S Y 3 0 0 L (gauge 5)
#check baseComposition S Y 0 0 L (gauge 5) (homOfLE (show 2 ≤ 3 by decide)) (homOfLE (show 3 ≤ 7 by decide))
end Gauge211
