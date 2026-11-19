import ContextualComposition.ContextadDisjointComparison
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage
namespace MovingDisjoint
noncomputable section
inductive Shade | white | black deriving DecidableEq
instance : Groupoid Shade where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  inv _ := ()
abbrev Gr := Nat × Shade
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of Gr)
  extend _ := CategoryTheory.Prod.fst Nat Shade
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
def hue (i : Nat) := if i = 0 then Shade.white else Shade.black
def tag (x : Nat) : Gr := (0,hue x)
def mGrade : (power S 2).apex ⥤ Apex P where
  obj x := pair _ _ ((power S 2).source.obj x) (tag ((power S 2).source.obj x))
  map f := arrow ((power S 2).source.map f) (𝟙 (0 : Nat),())
  map_id _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
  map_comp _ _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) HEq.rfl)
def m : ContextadTotal.Native S where
  grade := mGrade
  over := rfl
  delta := {app := fun _ => homOfLE (Nat.zero_le _)}
  cart {x y} f _ := by
    let b : hue ((power S 2).source.obj x) ⟶ hue ((power S 2).source.obj y) := ()
    let k : tag ((power S 2).source.obj x) ⟶ tag ((power S 2).source.obj y) := (𝟙 (0:Nat),b)
    have : IsIso k := by exact ⟨(𝟙 (0:Nat),inv b),rfl,rfl⟩
    have : IsIso (payloadMap (mGrade.map f)) := (inferInstance : IsIso k)
    exact ContextadCartesian.cart_of_payload _ _ (mGrade.map f)
def row : (power S 4).apex := pair _ _ (pair _ _ (pair _ _ (pair _ _ (3:Nat) ((1,Shade.white):Gr)) ((4,Shade.white):Gr)) ((2,Shade.white):Gr)) ((3,Shade.white):Gr)
abbrev op := ContextadRoutes.tensor m
example : ¬ IsIso (op.leg.app ((NativeAssoc.front S 3 ⋙ NativeAssoc.front S 2).obj row)) := by
  intro h
  obtain ⟨j,_,_⟩ := h.out
  exact (by decide : ¬ (4:Nat) ≤ 0) (leOfHom j)
end
end MovingDisjoint
namespace MovingDisjoint
open ContextadDisjointCut ContextadRoutes
noncomputable section
abbrev shadeOf (z : Apex P) : Shade := (payload P.grades (𝟭 Nat) z).2
def lastShade (z : (power S 2).apex) := shadeOf ((NativeAssoc.last S 1).obj z)
theorem leftWhite : lastShade ((lhs op op).grade.obj row) = Shade.white := by
  have h := Functor.congr_obj (leftTail op op) row
  exact (congrArg shadeOf h).trans rfl
theorem rightBlack : lastShade ((rhs op op).grade.obj row) = Shade.black := by
  have h := Functor.congr_obj (rightTail op) row
  obtain ⟨e,_⟩ := ContextadSchedule.snocPure (S := S) (i := 2) (j := 1) op ((inside 2 op).grade.obj row)
  exact (congrArg Prod.snd e).trans ((congrArg shadeOf h).trans rfl)
theorem notSame : (lhs op op).grade.obj row ≠ (rhs op op).grade.obj row := by
  intro h
  cases (leftWhite.symm.trans ((congrArg lastShade h).trans rightBlack))
theorem needsComparison : lhs op op ≠ rhs op op := by intro e; apply notSame; rw [e]
example : (lhs op op).grade.obj row ≅ (rhs op op).grade.obj row := (disjoint op op m.cart).grade.app row
end
end MovingDisjoint
