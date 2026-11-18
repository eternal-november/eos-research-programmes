import ContextualComposition.NativeTriple
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeAssoc SpanApex
namespace ParallelTriple
inductive G | pt
instance : Category G where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp := by intros; apply List.nil_append
  comp_id := by intros; apply List.append_nil
  assoc := by intros; apply List.append_assoc
abbrev B := Discrete Unit
def pt : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of G)
  extend _ := (Functor.const _).obj pt
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl, fun _ _ => HEq.rfl⟩
def atom := pair P.grades (𝟭 B) pt G.pt
def a : tel S := ⟨1,atom⟩
def z : tel S := ⟨0,pt⟩
def row := (show (word S 2).apex from ⟨a,z,rfl⟩)
def r : strings S := ⟨2,row⟩
def s : strings S := ⟨1,a⟩
def t : (Three.level S 2).apex := ⟨r,s,rfl⟩
def x : Three.strings3 S := ⟨2,t⟩
def letter (l : List Nat) : a ⟶ a := (incl S 1).map (arrow (𝟙 pt) l)
def line (l : List Nat) : r ⟶ r := (outer S 2).map ⟨⟨letter l,𝟙 z,Subsingleton.elim _ _⟩⟩
def edge (l : List Nat) : x ⟶ x := (Three.incl3 S 2).map ⟨⟨line l,(outer S 1).map (letter [8]),Subsingleton.elim _ _⟩⟩
def f := edge [1,2]
def g := edge [5]
theorem notComm : f ≫ g ≠ g ≫ f := by
  intro e
  have e1 := (Three.incl3 S 2).map_injective e
  have e2 := congrArg (Strict.fst (Rows.dest S) (Rows.source S)).map e1
  have e3 := (outer S 2).map_injective e2
  have e4 := congrArg (Strict.fst (rightLeg S) (leftLeg S)).map e3
  have e5 := (incl S 1).map_injective e4
  exact (by decide : [1,2,5] ≠ [5,1,2]) (congrArg (fun u : atom ⟶ atom => (show List Nat from payloadMap u)) e5)
noncomputable abbrev A := Three.mergeRows S ⋙ flatten S
noncomputable abbrev C := Three.mapRows S ⋙ flatten S
example : A.map f ≫ A.map g ≠ A.map g ≫ A.map f := by
  rw [← A.map_comp,← A.map_comp]
  let := Three.mergeFlattenFaithful S
  exact fun h => notComm (A.map_injective h)
example : C.map f ≫ C.map g ≠ C.map g ≫ C.map f := by
  rw [← C.map_comp,← C.map_comp]
  exact fun h => notComm (C.map_injective h)
example : TelescopeSquares.Aligned (A.map (f ≫ g)) (C.map (f ≫ g)) :=
  NativeCube.functorAlign (Three.flatten_assoc S) (f ≫ g)
-- Endpoints and length never detect this reversal.
example : (leftLeg S).map (A.map (f ≫ g)) = (leftLeg S).map (A.map (g ≫ f)) := Subsingleton.elim _ _
example : (rightLeg S).map (A.map (f ≫ g)) = (rightLeg S).map (A.map (g ≫ f)) := Subsingleton.elim _ _
example : (A.obj x).1 = 2 := rfl
end ParallelTriple
