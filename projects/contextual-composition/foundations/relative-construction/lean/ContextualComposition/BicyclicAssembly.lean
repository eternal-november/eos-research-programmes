module

public import Mathlib.Algebra.PresentedMonoid.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.SingleObj

/-! The ordinary obstruction to universal conservative assembly in
the relative-construction manuscript, theorem `thm:bicyclic`. The common
free generator embeds as opposite generators in two copies of the
bicyclic monoid. -/

@[expose] public section
namespace ContextualComposition.BicyclicAssembly

open CategoryTheory

inductive Letter where | down | up

inductive Rel : FreeMonoid Letter → FreeMonoid Letter → Prop where
  | cancel : Rel (FreeMonoid.of .down * FreeMonoid.of .up) 1

abbrev Bicyclic := PresentedMonoid Rel
def down : Bicyclic := PresentedMonoid.of Rel .down
def up : Bicyclic := PresentedMonoid.of Rel .up

theorem down_up : down * up = 1 := PresentedMonoid.mk_eq_mk_of_rel Rel.cancel

def generator : Letter → Function.End Nat
  | .down => Nat.pred
  | .up => Nat.succ

def realize : Bicyclic →* Function.End Nat :=
  PresentedMonoid.lift generator (by
    intro x y h; cases h
    simp only [map_mul,FreeMonoid.lift_eval_of,map_one]
    rfl)

theorem up_down_ne : up * down ≠ 1 := by
  intro e
  have h := congrArg (fun w => realize w 0) e
  change 1 = 0 at h
  contradiction

theorem down_power (n x : Nat) : realize (down ^ n) x = x - n := by
  induction n generalizing x with
  | zero => simp; rfl
  | succ n ih =>
    rw [pow_succ,map_mul]
    change realize (down ^ n) (x-1) = x - (n+1)
    rw [ih]; omega

theorem up_power (n x : Nat) : realize (up ^ n) x = x + n := by
  induction n generalizing x with
  | zero => simp; rfl
  | succ n ih =>
    rw [pow_succ,map_mul]
    change realize (up ^ n) (x+1) = x + (n+1)
    rw [ih]; omega

abbrev Pure := Multiplicative Nat

def powerMap (a : Bicyclic) : Pure →* Bicyclic where
  toFun n := a ^ n.toAdd
  map_one' := pow_zero _
  map_mul' n m := pow_add _ n.toAdd m.toAdd

def leftPure := (powerMap down).toFunctor
def rightPure := (powerMap up).toFunctor

instance : leftPure.Faithful where
  map_injective := by
    intro _ _ f g h
    change Pure at f g
    have e := congrArg (fun z => realize z (f.toAdd+g.toAdd)) h
    change realize (down ^ f.toAdd) _ = realize (down ^ g.toAdd) _ at e
    rw [down_power,down_power] at e
    change f.toAdd = g.toAdd
    omega

instance : rightPure.Faithful where
  map_injective := by
    intro _ _ f g h
    change Pure at f g
    have e := congrArg (fun z => realize z 0) h
    change realize (up ^ f.toAdd) _ = realize (up ^ g.toAdd) _ at e
    change f.toAdd = g.toAdd
    simpa only [up_power,Nat.zero_add] using e

abbrev point := SingleObj.star Bicyclic
abbrev low : point ⟶ point := down
abbrev high : point ⟶ point := up

theorem high_low : high ≫ low = 𝟙 point := down_up
theorem low_high_ne : low ≫ high ≠ 𝟙 point := up_down_ne

variable {D : Type*} [Category* D] (F G : SingleObj Bicyclic ⥤ D)

/-- Agreement on the generator up to a single invertible change of object
already forces collapse on both sides. -/
theorem common_collapse (i : F.obj point ≅ G.obj point)
    (h : F.map low ≫ i.hom = i.hom ≫ G.map high) :
    F.map (low ≫ high) = F.map (𝟙 point) ∧ G.map (low ≫ high) = G.map (𝟙 point) := by
  let c := i.hom ≫ G.map low ≫ i.inv
  have fg : F.map high ≫ F.map low = 𝟙 _ := by rw [← F.map_comp,high_low,F.map_id]
  have gg : G.map high ≫ G.map low = 𝟙 _ := by rw [← G.map_comp,high_low,G.map_id]
  have fc : F.map low ≫ c = 𝟙 _ := by
    dsimp [c]
    rw [← Category.assoc,h, Category.assoc,← Category.assoc (G.map high),gg]
    simp
  have bc : F.map high = c := by
    calc F.map high = F.map high ≫ (F.map low ≫ c) := by rw [fc,Category.comp_id]
         _ = c := by rw [← Category.assoc,fg,Category.id_comp]
  constructor
  · rw [F.map_comp,bc,fc,F.map_id]
  · rw [G.map_comp,G.map_id]
    apply (cancel_epi i.hom).mp
    have c' : F.map high ≫ i.hom = i.hom ≫ G.map low := by rw [bc]; simp [c]
    rw [← Category.assoc,← c',Category.assoc,← h,← Category.assoc,fg]
    simp

theorem no_faithful_assembly (i : leftPure ⋙ F ≅ rightPure ⋙ G) : ¬ F.Faithful ∧ ¬ G.Faithful := by
  let o := SingleObj.star Pure
  have k := i.hom.naturality (show o ⟶ o from (Multiplicative.ofAdd (1 : Nat) : Pure))
  have e : F.map low ≫ (i.app o).hom = (i.app o).hom ≫ G.map high := by
    change F.map (down ^ 1) ≫ _ = _ ≫ G.map (up ^ 1) at k
    simp only [pow_one] at k
    exact k
  have h := common_collapse F G (i.app o) e
  exact ⟨fun f => low_high_ne (F.map_injective h.1),fun g => low_high_ne (G.map_injective h.2)⟩

end ContextualComposition.BicyclicAssembly
