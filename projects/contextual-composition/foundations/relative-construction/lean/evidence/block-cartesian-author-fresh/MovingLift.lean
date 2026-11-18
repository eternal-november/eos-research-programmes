import ContextualComposition.BlockCartesian
import Mathlib.CategoryTheory.Category.Preorder
open CategoryTheory Opposite ContextualComposition.GrothendieckStep NativeBlocks NativeBlocks.Nested SpanApex NativeCleavage BlockCartesian
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
def target : strings S := ⟨3,⟨(tagPair S (1,0)).obj ⟨one 5 3,(8:Nat),rfl⟩,⟨2,two 8 5 7⟩,rfl⟩⟩
def J := All.nativeChoice S
def L := All.nestedChoice S J
def down : (2:Nat) ⟶ 5 := homOfLE (by decide)
def lift := L 2 target down
example : (All.source S).obj lift.obj = 2 := lift.source
example : (All.dest S).obj target = 20 := rfl
example : (All.dest S).obj lift.obj = 17 := rfl
example : lift.obj.1 = 3 := rfl
example : (count S 3 target.2) = 3 := rfl
example : ((flatten S).obj lift.obj).1 = 3 := rfl
theorem flatStrong : (leftLeg S).IsStronglyCartesian down ((flatten S).map lift.lift) :=
  (All.strongCartesian S down _).mp (chosenStrong lift)
example : ¬ IsIso ((flatten S).map lift.lift) := by
  intro hi
  let := hi
  let z := (leftLeg S).map (inv ((flatten S).map lift.lift))
  have b := Functor.congr_obj (flatten_source S) target
  have a := Functor.congr_obj (flatten_source S) lift.obj
  exact (by decide : ¬ 5 ≤ 2) (leOfHom ((eqToHom b.symm) ≫ z ≫ (eqToHom a)))

-- A nonconstant payload: indexing position i of the terminal context really matters.
def Y : Natᵒᵖ ⥤ Cat.{0,0} where
  obj n := Cat.of (Fin n.unop → Nat)
  map {a _} f := (Pi.comap (fun _ : Fin a.unop => Nat) (Fin.castLE f.unop.le)).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
def withPayload : Total Y (All.dest S) := pair Y _ target (fun i => i.val+8)
def weightedLift := All.nestedWeightedChoice S Y L 2 withPayload down
example : (payload Y _ weightedLift.obj) (⟨16,by decide⟩ : Fin 17) = 24 := rfl
example : (payload Y _ withPayload) (⟨19,by decide⟩ : Fin 20) = 27 := rfl
theorem weightedCart : (All.nativeProj S Y).IsStronglyCartesian down ((All.weighted S Y).map weightedLift.lift) :=
  (All.weightedStrong S Y down _).mp (chosenStrong weightedLift)
#check All.compLaw S Y L J (homOfLE (show 1 ≤ 2 by decide)) down
-- A vertical, noninvertible grade increase is not a cartesian lift of the identity.
def atom (n : Nat) : strings S := ⟨1,⟨1,one 2 n⟩⟩
def step : atom 3 ⟶ atom 5 :=
  (outer S 1).map ((incl S 1).map (arrow (x := one 2 3) (y := one 2 5) (𝟙 (2:Nat)) (show (3:Nat) ⟶ 5 from homOfLE (by decide))))
theorem noReverse (f : atom 5 ⟶ atom 3) : False := by
  rcases f with ⟨⟨f⟩⟩
  exact (by decide : ¬ 5 ≤ 3) (leOfHom (show (5:Nat) ⟶ 3 from payloadMap f))
example : ¬ (leftLeg S).IsStronglyCartesian (𝟙 (2:Nat)) ((flatten S).map step) := by
  intro h
  let := (All.strongCartesian S (𝟙 (2:Nat)) step).mpr h
  let : IsIso step := Functor.IsStronglyCartesian.isIso_of_base_isIso (All.source S) (𝟙 (2:Nat)) step
  exact noReverse (inv step)
def shift (n : Nat) : (Fin n → Nat) ⥤ (Fin n → Nat) where
  obj z i := z i + 3
  map f i := homOfLE (Nat.add_le_add_right (f i).le 3)
  map_id _ := rfl
  map_comp _ _ := rfl
def T : Y ⟶ Y where
  app n := (shift n.unop).toCatHom
  naturality _ _ _ := rfl
example : ((T.app (op 20)).toFunctor.obj (payload Y _ withPayload)) (⟨19,by decide⟩ : Fin 20) = 30 := rfl
def fibre : (All.nestedProj S Y).Fiber 5 := ⟨withPayload,rfl⟩
#check All.mixedLaw S L J T down fibre

def z0 (n : Nat) : strings S := ⟨0,n⟩
def z1 (n : Nat) : strings S := ⟨1,⟨0,n⟩⟩
def a0 : z0 2 ⟶ z0 5 := (outer S 0).map down
def a1 : z1 2 ⟶ z1 5 := (outer S 1).map ((incl S 0).map down)
def ing : Incoming (⟨0,(5:Nat)⟩ : tel S) := ⟨⟨0,(2:Nat)⟩,(incl S 0).map down⟩
example : liftInto (flatten S) (All.flattenIncoming S) (z0 5) ing = ⟨z0 2,a0⟩ := by
  apply (All.flattenIncoming S _).injective
  exact push_liftInto (flatten S) (All.flattenIncoming S) (z0 5) ing
example : liftInto (flatten S) (All.flattenIncoming S) (z1 5) ing = ⟨z1 2,a1⟩ := by
  apply (All.flattenIncoming S _).injective
  exact push_liftInto (flatten S) (All.flattenIncoming S) (z1 5) ing
example : z0 2 ≠ z1 2 := by intro e; cases congrArg Sigma.fst e
end Moving
