import ContextualComposition.MateLaws
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
namespace Whisker205
inductive P | pt
instance : Category P where
  Hom _ _ := Int
  id _ := 0
  comp f g := f + g
  id_comp := by intros; apply Int.zero_add
  comp_id := by intros; apply Int.add_zero
  assoc := by intros; apply Int.add_assoc
def scale (k : Int) : P ⥤ P where
  obj := id
  map f := k * (show Int from f)
  map_id _ := by change k*0 = 0; simp
  map_comp f g := by change Int at f g; exact Int.mul_add k f g
def iso (i : Int) (x : P) : x ≅ x := ⟨i,-i,Int.add_right_neg i,Int.add_left_neg i⟩
def shift (i : Int) : 𝟭 P ≅ 𝟭 P :=
  NatIso.ofComponents (iso i) (by intro x y h; exact Int.add_comm h i)
def twist (k : Int) : P ≌ P where
  functor := 𝟭 P
  inverse := 𝟭 P
  unitIso := shift k
  counitIso := shift (-k)
  functor_unitIso_comp := by intro; exact Int.add_right_neg k
def face (s t : Int) (K : P ⥤ P) : (twist s).functor ⋙ K ≅ K ⋙ (twist t).functor := eqToIso rfl
def back (s t : Int) (K : P ⥤ P) := SumChange.inverseSquare (twist s) (twist t) (face s t K)
def T := scale 2
def U := scale 3
example : (back 1 5 T).inv.app P.pt = (-3:Int) := rfl
example : (back 5 11 U).inv.app P.pt = (4:Int) := rfl
example : (back 1 11 (T ⋙ U)).inv.app P.pt = (-5:Int) := rfl
example : (back 1 11 (T ⋙ U)).inv.app P.pt ≠ (back 5 11 U).inv.app P.pt ≫ (back 1 5 T).inv.app P.pt := by
  change (-5:Int) ≠ 4 + -3; decide
example : FibreValue.Paste.CompLaw (back 1 11 (T ⋙ U)).symm (back 5 11 U).symm (back 1 5 T).symm
    (𝟙 (T ⋙ U)) (𝟙 (T ⋙ U)) :=
  MateLaws.comp (twist 11) (twist 5) (twist 1) _ _ _ _ _ (fun _ => rfl)
example : (back 5 5 (𝟭 P)).inv.app P.pt = (0:Int) := rfl
example : FibreValue.Paste.UnitLaw (back 5 5 (𝟭 P)).symm (𝟙 _) (𝟙 _) :=
  MateLaws.unit (twist 5) (face 5 5 (𝟭 P)) _ _ (fun _ => rfl)
-- Compute the *whiskered* first correction, not just the scalar total.
example : U.map ((back 1 5 T).inv.app P.pt) = (-9:Int) := rfl
end Whisker205
