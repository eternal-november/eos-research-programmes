import ContextualComposition.NativeBlocks
open CategoryTheory CategoryTheory.Limits Opposite ContextualComposition.GrothendieckStep NativeBlocks
namespace IsoBoundary
-- The comparison must accommodate an actual nonidentity boundary automorphism.
-- At length zero both native powers are the identity span of Type.
abbrev S := Families.splitEndpoints
def swap : Bool ≅ Bool where
  hom := ↾Bool.not
  inv := ↾Bool.not
  hom_inv_id := by ext b; cases b <;> rfl
  inv_hom_id := by ext b; cases b <;> rfl
def twisting : CategoricalPullback (power S 0).dest (power S 0).source := ⟨Bool,Bool,swap⟩
example : twisting.iso.hom ≠ 𝟙 _ := by
  intro h
  have k := congrArg (fun f : Bool ⟶ Bool => f false) h
  cases k
example : ∃ x : (power S (0+0)).apex, Nonempty ((equipment S 0 0).functor.obj x ≅ twisting) :=
  (equipment S 0 0).functor.objObjPreimageIso twisting |> fun i => ⟨_,⟨i⟩⟩
-- Here the obstruction to on-the-nose equality is witnessed, not postulated.
example (x : (power S (0+0)).apex) : (equipment S 0 0).functor.obj x ≠ twisting := by
  intro h
  have t : HEq ((equipment S 0 0).functor.obj x).iso.hom twisting.iso.hom := by rw [h]
  change HEq (𝟙 x) swap.hom at t
  have ex : x = Bool := congrArg CategoricalPullback.fst h
  cases ex
  have k := congrArg (fun f : Bool ⟶ Bool => f) (eq_of_heq t)
  exact (by intro j; cases (congrArg (fun f : Bool ⟶ Bool => f false) j) : swap.hom ≠ 𝟙 _) k.symm
end IsoBoundary
