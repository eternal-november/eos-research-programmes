import ContextualComposition.PayloadLaws
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep
namespace PayloadMate
inductive Pt | star
instance : Category Pt where
  Hom _ _ := Int
  id _ := 0
  comp f g := f + g
  id_comp := by intros; apply Int.zero_add
  comp_id := by intros; apply Int.add_zero
  assoc := by intros; apply Int.add_assoc
def edge (k : Int) (x : Pt) : x ≅ x where
  hom := k
  inv := -k
  hom_inv_id := Int.add_right_neg k
  inv_hom_id := Int.add_left_neg k
def shift (k : Int) : 𝟭 Pt ≅ 𝟭 Pt :=
  NatIso.ofComponents (edge k) (by intro x y f; exact Int.add_comm f k)
def twist (k : Int) : Pt ≌ Pt where
  functor := 𝟭 Pt
  inverse := 𝟭 Pt
  unitIso := shift k
  counitIso := shift (-k)
  functor_unitIso_comp := by intro x; exact Int.add_right_neg k
-- Identity forward faces; all three underlying functors are unchanged. Their
-- chosen equivalence units differ, so actual inverse faces are not identities.
def face (s t : Int) : (twist s).functor ⋙ 𝟭 Pt ≅ 𝟭 Pt ⋙ (twist t).functor := eqToIso rfl
def mate (s t : Int) := SumChange.inverseSquare (twist s) (twist t) (face s t)
example : (mate 2 7).inv.app Pt.star = (-5:Int) := rfl
example : (mate 7 17).inv.app Pt.star = (-10:Int) := rfl
example : (mate 2 17).inv.app Pt.star = (-15:Int) := rfl
example : (mate 2 17).inv.app Pt.star ≠ (mate 2 7).inv.app Pt.star ≫ 𝟙 _ := by
  change (-15:Int) ≠ -5 + 0; decide
example : FibreValue.Paste.CompLaw (mate 2 17).symm (mate 7 17).symm (mate 2 7).symm
    (𝟙 (𝟭 Pt)) (𝟙 (𝟭 Pt)) :=
  MateLaws.comp (twist 17) (twist 7) (twist 2) _ _ _ _ _ (fun _ => rfl)
end PayloadMate
