import ContextualComposition.NativeBlocks
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks SpanApex
namespace Moving
def extend (a : Nat) : Nat ⥤ Nat where
  obj k := a+k
  map f := homOfLE (Nat.add_le_add_left f.le a)
  map_id _ := rfl
  map_comp _ _ := rfl
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Nat)
  extend := extend
  lift {a d} f := { app := fun k => homOfLE (Nat.add_le_add_right f.le k) }
theorem S : P.Split := ⟨fun _ => HEq.rfl, fun _ _ => HEq.rfl⟩
def one (A g : Nat) : (power S 1).apex := pair P.grades (𝟭 Nat) A g
def two (A g h : Nat) : (power S 2).apex := pair _ _ (one A g) h
def three (A g h j : Nat) : (power S 3).apex := pair _ _ (two A g h) j
def legs (A g h j : Nat) : part S (1,2) := ⟨one A g,two (A+g) h j,rfl⟩
def a : one 1 2 ⟶ one 2 3 := arrow (x := _) (y := _) (homOfLE (show 1 ≤ 2 by decide)) (show (2:Nat) ⟶ 3 from homOfLE (by decide))
def b : two 3 3 5 ⟶ two 5 4 7 := arrow (x := _) (y := _)
  (arrow (x := one 3 3) (y := one 5 4) (show (3:Nat) ⟶ 5 from homOfLE (by decide)) (show (3:Nat) ⟶ 4 from homOfLE (by decide))) (show (5:Nat) ⟶ 7 from homOfLE (by decide))
def moving : legs 1 2 3 5 ⟶ legs 2 3 4 7 := ⟨⟨a,b,Subsingleton.elim _ _⟩⟩
theorem notIso : ¬ IsIso moving := by
  intro h
  have z := (Strict.fst (power S 1).dest (power S 2).source).map (inv moving)
  exact (by decide : ¬ 2 ≤ 1) (leOfHom (gradeMap z))
example : (power S 2).dest.obj (legs 1 2 3 5).snd = 11 := rfl
example : (power S 2).dest.obj (legs 2 3 4 7).snd = 16 := rfl

noncomputable abbrev join := (blocks S 1 2).joinFunctor
noncomputable abbrev cut := (blocks S 1 2).cutFunctor
-- Retain both noninvertible moving pieces on the full morphism, after flattening and cutting again.
example : TelescopeSquares.Aligned ((cut.map (join.map moving)).hom.fst) a :=
  NativeCube.functorAlign (blocks S 1 2).join_first moving
example : TelescopeSquares.Aligned ((cut.map (join.map moving)).hom.snd) b :=
  NativeCube.functorAlign (blocks S 1 2).join_rest moving
example : ¬ IsIso (join.map moving) := by
  intro h
  let ff := (blocks S 1 2).strictIso.symm.toEquivalence.fullyFaithfulFunctor
  let : IsIso ((blocks S 1 2).strictIso.symm.toEquivalence.functor.map moving) := h
  exact notIso (Functor.FullyFaithful.isIso_of_isIso_map ff moving)
-- Independently inspect the raw snoc apex at each position, without using cut as a decoder.
abbrev firstOfThree : (power S 3).apex ⥤ (power S 1).apex := gradeProjection ⋙ gradeProjection
abbrev midOfThree : (power S 3).apex ⥤ (power S 1).apex := gradeProjection ⋙ second P (power S 1).dest
abbrev lastOfThree : (power S 3).apex ⥤ (power S 1).apex := second P (power S 2).dest
abbrev headOfTwo : (power S 2).apex ⥤ (power S 1).apex := gradeProjection
abbrev lastOfTwo : (power S 2).apex ⥤ (power S 1).apex := second P (power S 1).dest
theorem firstProjection : join ⋙ firstOfThree = Strict.fst _ _ := (blocks S 1 2).join_first
theorem lastProjection : join ⋙ lastOfThree = Strict.snd _ _ ⋙ lastOfTwo := by
  have h : (blocks S 1 2).rest ⋙ lastOfTwo = lastOfThree := Cut.nextRest_grade S (blocks S 1 1)
  exact (congrArg (join ⋙ ·) h.symm).trans (congrArg (· ⋙ lastOfTwo) (blocks S 1 2).join_rest)
theorem midProjection : join ⋙ midOfThree = Strict.snd _ _ ⋙ headOfTwo := by
  have h : (blocks S 1 2).rest ⋙ headOfTwo = gradeProjection ⋙ (blocks S 1 1).rest := Cut.nextRest_pre S (blocks S 1 1)
  have j : (blocks S 1 1).rest = lastOfTwo := Cut.nextRest_grade S (emptyCut S (power S 1))
  exact (congrArg (join ⋙ ·) ((h.trans (congrArg (gradeProjection ⋙ ·) j)).symm)).trans
    (congrArg (· ⋙ headOfTwo) (blocks S 1 2).join_rest)
noncomputable abbrev output := join.obj (legs 2 3 4 7)
example : (payload _ _ (firstOfThree.obj output),payload _ _ (midOfThree.obj output),payload _ _ (lastOfThree.obj output)) =
    ((3:Nat),(4:Nat),(7:Nat)) := by
  rw [show firstOfThree.obj output = one 2 3 from Functor.congr_obj firstProjection _,
    show midOfThree.obj output = one 5 4 from Functor.congr_obj midProjection _,
    show lastOfThree.obj output = one 9 7 from Functor.congr_obj lastProjection _]
  rfl
example : TelescopeSquares.Aligned (midOfThree.map (join.map moving)) (headOfTwo.map b) :=
  NativeCube.functorAlign midProjection moving
def tagged := tagPair S (1,2)
noncomputable def nestedJoin := tagged ⋙ Nested.outer S 2 ⋙ Nested.flatten S
theorem nativeFunctors : nestedJoin = join ⋙ incl S 3 :=
  (congrArg (tagged ⋙ ·) (Nested.flatten_two S)).trans (binary_at S 1 2)
-- The summed native output is not just a length calculation.
example : TelescopeSquares.Aligned (nestedJoin.map moving) ((incl S 3).map (join.map moving)) :=
  NativeCube.functorAlign nativeFunctors moving
-- Actual words of blocks, including empty inner blocks. The third block extends from 6 to 11.
def ragged : (Nested.word S 3).apex := ⟨(tagPair S (2,0)).obj
  ⟨two 1 2 3,(6:Nat),rfl⟩,⟨1,one 6 5⟩,rfl⟩
example : ((Nested.flatten S).obj ⟨3,ragged⟩).1 = 3 := rfl
example : (Nested.word S 3).dest.obj ragged = 11 := rfl
example : (rightLeg S).obj ((Nested.flatten S).obj ⟨3,ragged⟩) = 11 :=
  Functor.congr_obj (Nested.flatten_dest S) ⟨3,ragged⟩
example : (Nested.flatten S).obj ⟨0,(8:Nat)⟩ = ⟨0,(8:Nat)⟩ := rfl
example : (Nested.flatten S).obj ⟨1,⟨0,(8:Nat)⟩⟩ = ⟨0,(8:Nat)⟩ := rfl
#check Nested.singletons_flatten S
end Moving
