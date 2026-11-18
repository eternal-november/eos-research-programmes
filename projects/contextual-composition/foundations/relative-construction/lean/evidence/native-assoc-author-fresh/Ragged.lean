import ContextualComposition.NativeTriple
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested NativeAssoc
namespace RaggedTriple
def extend (a : Nat) : Nat ⥤ Nat where
  obj k := 10*a+k
  map f := homOfLE (Nat.add_le_add_left f.le _)
  map_id _ := rfl
  map_comp _ _ := rfl
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend := extend
  lift {a d} f := { app := fun k => homOfLE (Nat.add_le_add_right (Nat.mul_le_mul_left 10 f.le) k) }
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def one (a g : Nat) : tel S := ⟨1,pair P.grades (𝟭 Nat) a g⟩
def empty (a : Nat) : tel S := ⟨0,a⟩
-- two rows of two blocks, with a genuinely empty middle block.
def first (a : Nat) : strings S := ⟨2,⟨one a 2,empty (10*a+2),rfl⟩⟩
def second (a : Nat) : strings S := ⟨2,⟨one a 3,one (10*a+3) 4,rfl⟩⟩
def element (a : Nat) : Three.strings3 S := ⟨2,⟨first a,second (10*a+2),rfl⟩⟩
def merged (a : Nat) : strings S :=
  ⟨4,⟨⟨⟨one a 2,empty (10*a+2),rfl⟩,one (10*a+2) 3,rfl⟩,one (10*(10*a+2)+3) 4,rfl⟩⟩
example (a : Nat) : (Three.mergeRows S).obj (element a) = merged a := rfl
example : ((Three.mergeRows S).obj (element 1)).1 = 4 := rfl
example : ((Three.mapRows S).obj (element 1)).1 = 2 := rfl
example : (Three.mergeRows S).obj (element 1) ≠ (Three.mapRows S).obj (element 1) := by
  intro e; exact (by decide : 4 ≠ 2) (congrArg Sigma.fst e)
noncomputable abbrev lhs := Three.mergeRows S ⋙ flatten S
noncomputable abbrev rhs := Three.mapRows S ⋙ flatten S
example : lhs.obj (element 1) = rhs.obj (element 1) := Functor.congr_obj (Three.flatten_assoc S) _
example : (lhs.obj (element 1)).1 = 3 := rfl
theorem endPt (a : Nat) : (rightLeg S).obj (lhs.obj (element a)) = 10*(10*(10*a+2)+3)+4 :=
  (Functor.congr_obj (flatten_dest S) ((Three.mergeRows S).obj (element a))).trans (Functor.congr_obj (Three.merge_dest S) (element a))
example : (rightLeg S).obj (lhs.obj (element 1)) = 1234 := endPt 1
example : (rightLeg S).obj (rhs.obj (element 1)) ≠ 1432 := by
  rw [← Functor.congr_obj (Three.flatten_assoc S) (element 1),endPt]; decide
def onOne {a d g : Nat} (h : a ≤ d) : one a g ⟶ one d g :=
  (incl S 1).map (arrow (homOfLE h) (𝟙 g))
def onFirst {a d : Nat} (h : a ≤ d) : first a ⟶ first d :=
  (outer S 2).map ⟨⟨onOne h,(incl S 0).map (show (10*a+2:Nat) ⟶ 10*d+2 from homOfLE (Nat.add_le_add_right (Nat.mul_le_mul_left 10 h) 2)),Subsingleton.elim _ _⟩⟩
def onSecond {a d : Nat} (h : a ≤ d) : second a ⟶ second d :=
  (outer S 2).map ⟨⟨onOne h,onOne (Nat.add_le_add_right (Nat.mul_le_mul_left 10 h) 3),Subsingleton.elim _ _⟩⟩
def f : element 1 ⟶ element 2 := (Three.incl3 S 2).map ⟨⟨onFirst (by decide),onSecond (by decide),Subsingleton.elim _ _⟩⟩
example : TelescopeSquares.Aligned (lhs.map f) (rhs.map f) := NativeCube.functorAlign (Three.flatten_assoc S) f
example : ¬ IsIso (lhs.map f) := by
  intro h; let := h
  have s {a : Nat} : (leftLeg S).obj (lhs.obj (element a)) = a :=
    (Functor.congr_obj (flatten_source S) ((Three.mergeRows S).obj (element a))).trans (Functor.congr_obj (Three.merge_source S) (element a))
  exact (by decide : ¬ 2 ≤ 1) (leOfHom ((eqToHom s.symm) ≫ (leftLeg S).map (inv (lhs.map f)) ≫ eqToHom s))
-- The payload varies with the terminal decimal context.
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj n := Cat.of (Fin n.unop → Nat)
  map {a _} f := (Pi.comap (fun _ : Fin a.unop => Nat) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def weighted (a : Nat) : Total Y (Three.dest S) := pair Y _ (element a) (fun i => i.val+1)
def wf : weighted 1 ⟶ weighted 2 := arrow f (fun _ => homOfLE (le_refl _))
example : (payload Y _ (weighted 1)) ⟨1233,by decide⟩ = 1234 := rfl
example : (payload Y _ (weighted 2)) ⟨2233,by decide⟩ = 2234 := rfl
example : TelescopeSquares.Aligned ((Three.weightedOuter S Y ⋙ BlockCartesian.All.weighted S Y).map wf)
    ((Three.weightedInner S Y ⋙ BlockCartesian.All.weighted S Y).map wf) := NativeCube.functorAlign (Three.weighted_assoc S Y) wf
noncomputable abbrev wL := Three.weightedOuter S Y ⋙ BlockCartesian.All.weighted S Y
example : HEq (payload Y (rightLeg S) (wL.obj (weighted 1))) (payload Y (Three.dest S) (weighted 1)) :=
  (SpanPayload.total_payload_obj Y (flatten S) (rightLeg S) (flatten_dest S) ((Three.weightedOuter S Y).obj (weighted 1))).trans
    (SpanPayload.total_payload_obj Y (Three.mergeRows S) (Rows.dest S) (Three.merge_dest S) (weighted 1))
def threeRows (a : Nat) : Three.strings3 S :=
  ⟨3,⟨⟨first a,⟨0,(10*a+2:Nat)⟩,rfl⟩,second (10*a+2),rfl⟩⟩
example (a : Nat) : (Three.mergeRows S).obj (threeRows a) = merged a := rfl
example (a : Nat) : ((Three.mapRows S).obj (threeRows a)).1 = 3 := rfl
example (a : Nat) : rhs.obj (threeRows a) = lhs.obj (element a) := by
  rw [← Functor.congr_obj (Three.flatten_assoc S) (threeRows a)]
  rfl
def outerEmpty : Three.strings3 S := ⟨0,(7:Nat)⟩
def oneEmptyRow : Three.strings3 S := ⟨1,⟨0,(7:Nat)⟩⟩
example : ((Three.mergeRows S).obj oneEmptyRow).1 = 0 := rfl
example : ((Three.mapRows S).obj oneEmptyRow).1 = 1 := rfl
example : lhs.obj oneEmptyRow = lhs.obj outerEmpty := rfl
end RaggedTriple
