import ContextualComposition.MixedMates
open CategoryTheory CategoryTheory.Functor ContextualComposition.GrothendieckStep
open MixedMates TaggedMixed
namespace FourCorners
inductive P | star
instance : Category P where
  Hom _ _ := Int × Nat
  id _ := (0,0)
  comp f g := (f.1 + g.1,f.2 + g.2)
  id_comp := by intros; apply Prod.ext <;> simp
  comp_id := by intros; apply Prod.ext <;> simp
  assoc := by intros; apply Prod.ext <;> simp [Int.add_assoc,Nat.add_assoc]
def shift (k : Int) : 𝟭 P ≅ 𝟭 P :=
  NatIso.ofComponents (fun _ => ⟨(k,0),(-k,0),Prod.ext (Int.add_right_neg k) rfl,Prod.ext (Int.add_left_neg k) rfl⟩)
    (by intro x y h; exact Prod.ext (Int.add_comm h.1 k) (Nat.add_comm h.2 0))
def twist (k : Int) : P ≌ P where
  functor := 𝟭 P
  inverse := 𝟭 P
  unitIso := shift k
  counitIso := shift (-k)
  functor_unitIso_comp := by intro x; exact @Prod.ext Int Nat (k + -k,0) (0,0) (Int.add_right_neg k) rfl
def grid (k : Int) : FinalCube.Mix.Grid where
  A := P; D := P; A' := P; D' := P
  b := 𝟭 P; b' := 𝟭 P; p := 𝟭 P; q := 𝟭 P
  cell := { app := fun _ => (k,1), naturality := by
              intro x y h; exact Prod.ext (Int.add_comm h.1 k) (Nat.add_comm h.2 1) }
-- The mixed cell is noninvertible: the natural-number coordinate cannot return to zero.
example (k : Int) : ¬ IsIso ((grid k).cell.app P.star) := by
  intro h
  obtain ⟨g,e,_⟩ := h.out
  have q := congrArg Prod.snd e
  change 1 + g.2 = 0 at q
  omega
def M : Frame (grid 15) (grid 4) where
  f := twist 5; g := twist 2; f' := twist 11; g' := twist 17
  s := shift 4; t := shift 7; l := shift 1; r := shift 9
theorem forwardOK : Cube.Law M.forward := by intro x; rfl
example : Cube.Law M.reverse.forward := M.backLaw forwardOK
-- The chosen corrections are not obtained by merely reversing the signs of the forward faces.
example : M.reverse.forward.s.app P.star = ((1:Int),(0:Nat)) := rfl
example : M.reverse.forward.t.app P.star = ((13:Int),(0:Nat)) := rfl
example : M.reverse.forward.l.app P.star = ((-5:Int),(0:Nat)) := rfl
example : M.reverse.forward.r.app P.star = ((-6:Int),(0:Nat)) := rfl
example : M.reverse.forward.t.app P.star ≠ M.t.hom.app P.star := by change ((13:Int),(0:Nat)) ≠ (7,0); decide
-- Both actual paths have positive second coordinate: no inversion of the mixed cell took place.
example : (M.reverse.forward.f'.map ((grid 4).cell.app P.star) ≫ M.reverse.forward.t.app P.star) ≫
    (grid 15).b'.map (M.reverse.forward.r.app P.star) = ((11:Int),(1:Nat)) := rfl
end FourCorners
