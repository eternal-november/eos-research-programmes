import ContextualComposition.NativeBlocks
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks
open SpanApex
namespace Ragged207
abbrev B := Discrete (List Nat)
abbrev Grade := Discrete Nat
def ext (a : B) : Grade ⥤ B := Discrete.functor (fun n => ⟨a.as ++ [n]⟩)
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of Grade)
  extend := ext
  lift {A D} f := by
    have e : D = A := Discrete.ext (Discrete.eq_of_hom f)
    subst D; exact 𝟙 _
theorem S : P.Split where
  lift_id _ := by apply heq_of_eq; apply Subsingleton.elim
  lift_comp _ _ := by apply heq_of_eq; apply Subsingleton.elim
def one (a : List Nat) (j : Nat) : (power S 1).apex := pair P.grades (𝟭 B) (Discrete.mk a) (Discrete.mk j)
def two (a : List Nat) (i j : Nat) : (power S 2).apex := pair _ _ (one a i) (Discrete.mk j)
def data : (Nested.word S 3).apex :=
  ⟨(tagPair S (1,0)).obj ⟨one [9] 5,Discrete.mk [9,5],rfl⟩,⟨2,two [9,5] 8 2⟩,rfl⟩
def elems (z : tel S) := ((rightLeg S).obj z).as
example : (Nested.count S 3 data) = 3 := rfl
example : ((Nested.flatten S).obj ⟨3,data⟩).1 = 3 := rfl
example : elems ((Nested.flatten S).obj ⟨3,data⟩) = [9,5,8,2] :=
  congrArg Discrete.as (Functor.congr_obj (Nested.flatten_dest S) ⟨3,data⟩)
example : elems ((Nested.flatten S).obj ⟨3,data⟩) ≠ [9,2,8,5] := by
  have e : elems ((Nested.flatten S).obj ⟨3,data⟩) = [9,5,8,2] :=
    congrArg Discrete.as (Functor.congr_obj (Nested.flatten_dest S) ⟨3,data⟩)
  rw [e]; decide
example : ((leftLeg S).obj ((Nested.flatten S).obj ⟨3,data⟩)).as = [9] :=
  congrArg Discrete.as (Functor.congr_obj (Nested.flatten_source S) ⟨3,data⟩)
def z0 : Nested.strings S := ⟨0,Discrete.mk [1]⟩
def z1 : Nested.strings S := ⟨1,⟨0,Discrete.mk [1]⟩⟩
example : (Nested.flatten S).obj z0 = (Nested.flatten S).obj z1 := rfl
theorem noArrow (f : z0 ⟶ z1) : False := by cases f
example : ¬ (Nested.flatten S).Full := by
  intro h
  let : (Nested.flatten S).Full := h
  exact noArrow ((Nested.flatten S).preimage (X := z0) (Y := z1) (𝟙 ((Nested.flatten S).obj z0)))
example (m : Nat) : (blocks S m 0).joinFunctor = Strict.fst (power S m).dest (power S 0).source :=
  (blocks S m 0).join_first
end Ragged207
