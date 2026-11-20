import ContextualComposition.AmbientSuffixMateRead
import ContextualComposition.AmbientDisjointFrames
import ContextualComposition.AmbientExchangeDemand
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
namespace MovingSuffixProbe
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
noncomputable section
set_option backward.isDefEq.respectTransparency false
inductive O | pt
instance : Groupoid O where
  Hom _ _ := Bool
  id _ := false
  comp a b := xor a b
  inv a := a
  id_comp := by intro _ _ f; cases f <;> rfl
  comp_id := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl
  inv_comp := by intro _ _ f; cases f <;> rfl
  comp_inv := by intro _ _ f; cases f <;> rfl
def G : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of O)
def shade (n : Nat) := decide (n=0)
def sign (x : O) (t : Bool) : x ≅ x where
  hom := t
  inv := t
  hom_inv_id := by cases t <;> rfl
  inv_hom_id := by cases t <;> rfl
def twistAt (i j : Nat) : 𝟭 O ≅ 𝟭 O := NatIso.ofComponents (fun x => sign x (xor (shade i) (shade j)))
  (fun {x y} f => by change xor f _ = xor _ f; cases shade i <;> cases shade j <;> cases f <;> rfl)
def face {i j : Nat} (a : i ⟶ j) : (G.map a.op).toFunctor ⋙ 𝟭 O ≅ 𝟭 O ⋙ (G.map a.op).toFunctor := twistAt i j
def alpha : CategoryTheory.Pseudofunctor.StrongTrans G.toPseudofunctor' G.toPseudofunctor' :=
  ContextadStrong.assemble (G := G) (H := G) (fun _ => 𝟭 O) (fun a => face a)
    (fun i x => by simp only [eqToHom_app]; change xor (xor (shade i) (shade i)) false = false; cases shade i <;> rfl)
    (fun {i j k} a b x => by simp only [eqToHom_app]; change xor (xor (shade i) (shade k)) false = xor false (xor (xor (shade i) (shade j)) (xor (shade j) (shade k))); cases shade i <;> cases shade j <;> cases shade k <;> rfl)
open AmbientCoordinates AmbientBicategory ContextadRoutes ContextadWeakWeight AmbientSuffixRoutes MovingDisjoint
abbrev Z : Obj.{0,0} Nat := G
noncomputable abbrev f : Z ⟶ Z := CategoryTheory.Bicategory.InducedBicategory.mkHom alpha
def sourceRow : Raw S Z 3 := pair _ _ ((NativeAssoc.front S 3).obj MovingDisjoint.row) O.pt
theorem directed : ¬ IsIso (op.leg.app ((NativeAssoc.front S 2).obj (grade _ _ sourceRow))) := by
  intro h; obtain ⟨j,_,_⟩ := h.out; exact (by decide : ¬(4:Nat) ≤ 0) (leOfHom j)
set_option linter.defProp false in
def staged := @AmbientSuffixMateRead.read Nat _ P S Z Z f _ _ op sourceRow
set_option linter.defProp false in
def cone := @AmbientSuffixCorridor.packed Nat _ P S Z Z f _ _ op sourceRow
theorem distinctPayload : (false : O.pt ⟶ O.pt) ≠ true := Bool.false_ne_true
end
end MovingSuffixProbe
#print axioms MovingSuffixProbe.staged
#print axioms MovingSuffixProbe.cone
