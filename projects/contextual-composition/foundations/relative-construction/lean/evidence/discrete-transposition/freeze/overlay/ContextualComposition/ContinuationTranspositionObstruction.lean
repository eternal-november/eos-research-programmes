module

public import ContextualComposition.DiscreteTransposition
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Issue #105, discrete-transposition obstruction, Wreath-extension candidates §8.
The finite witness uses the continuation monad with Boolean answers, on `Type 0`. -/

namespace ContextualComposition.ContinuationTranspositionObstruction
open CategoryTheory CategoryTheory.Limits
open ContextualComposition.DiscreteTransposition
universe u

/-- Continuations with Boolean answers. -/
abbrev Cont (B : Type u) := (B → Bool) → Bool

/-- Postcomposition in the continuation functor is precomposition on predicates. -/
def continuationFunctor : Type u ⥤ Type u where
  obj := Cont
  map f := TypeCat.ofHom fun k p => k (fun x => p (f x))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The genuine continuation monad: the unit evaluates, and multiplication
passes an evaluation functional to a higher-order continuation. -/
def continuationMonad : CategoryTheory.Monad (Type u) where
  toFunctor := continuationFunctor
  η := { app := fun _ => TypeCat.ofHom fun x p => p x, naturality := by intros; rfl }
  μ := { app := fun _ => TypeCat.ofHom fun K p => K (fun k => k p), naturality := by intros; rfl }
  assoc _ := rfl
  left_unit _ := rfl
  right_unit _ := rfl

theorem continuation_map {B C : Type u} (f : B ⟶ C) (k : Cont B) (p : C → Bool) :
    continuationMonad.map f k p = k (fun x => p (f x)) := rfl

/-- The single map into the terminal object, used for both cospan legs. -/
def toUnit : Bool ⟶ Unit := TypeCat.ofHom fun _ => ()

private def sourceApexEquiv : Types.PullbackObj toUnit toUnit ≃ Bool × Bool where
  toFun := Subtype.val
  invFun p := ⟨p, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev Fiber (t : Cont Unit) :=
  { k : Cont Bool // continuationMonad.map toUnit k = t }

/-- Under the actual terminal leg, only constant predicates are read. -/
theorem terminal_map (k : Cont Bool) (p : Unit → Bool) :
    continuationMonad.map toUnit k p = k (fun _ => p ()) := rfl

/-- Reconstruct a continuation from its terminal image and its two free values. -/
def extendFiber (t : Cont Unit) (v : Bool × Bool) (p : Bool → Bool) : Bool :=
  if p false then
    if p true then t (fun _ => true) else v.2
  else
    if p true then v.1 else t (fun _ => false)

/-- Over any continuation on the singleton, exactly the values on identity and
negation remain free; the inverse extends by those two values. -/
def fiberEquiv (t : Cont Unit) : Fiber t ≃ Bool × Bool where
  toFun k := (k.1 id, k.1 Bool.not)
  invFun v := ⟨extendFiber t v, by
    funext p
    have hp : (fun _ : Unit => p ()) = p := by
      funext x
      cases x
      rfl
    rw [terminal_map, ← hp]
    cases p () <;> rfl⟩
  left_inv k := by
    apply Subtype.ext
    funext p
    have hs (b : Bool) : k.1 (fun _ => b) = t (fun _ => b) :=
      congrFun k.2 (fun _ => b)
    cases h₀ : p false <;> cases h₁ : p true
    · have hp : p = (fun _ => false) := by
        funext x
        cases x <;> assumption
      simp [extendFiber, hp, hs]
    · have hp : p = id := by
        funext x
        cases x <;> assumption
      rw [hp]
      rfl
    · have hp : p = Bool.not := by
        funext x
        cases x <;> assumption
      rw [hp]
      rfl
    · have hp : p = (fun _ => true) := by
        funext x
        cases x <;> assumption
      simp [extendFiber, hp, hs]
  right_inv _ := rfl

theorem fiber_card (t : Cont Unit) : Nat.card (Fiber t) = 4 := by
  rw [Nat.card_congr (fiberEquiv t)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool]

/-- Identify the actual subtype by choosing its common image, not by dropping the equality. -/
def targetFibers : MappedPullback continuationMonad.toFunctor toUnit toUnit ≃
    Σ t : Cont Unit, Fiber t × Fiber t where
  toFun x := ⟨continuationMonad.map toUnit x.1.1, ⟨x.1.1, rfl⟩, ⟨x.1.2, x.2.symm⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), x.2.1.2.trans x.2.2.2.symm⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨t, ⟨k, hk⟩, ⟨l, hl⟩⟩
    subst t
    rfl

private def sourceEquiv : Cont (Types.PullbackObj toUnit toUnit) ≃ Cont (Bool × Bool) :=
  (sourceApexEquiv.arrowCongr (Equiv.refl Bool)).arrowCongr (Equiv.refl Bool)

/-- The actual domain of the continuation comparison has cardinality 65,536. -/
theorem source_card :
    Nat.card (continuationMonad.obj (Types.PullbackObj toUnit toUnit)) = 65536 := by
  change Nat.card (Cont (Types.PullbackObj toUnit toUnit)) = 65536
  rw [Nat.card_congr sourceEquiv]
  simp only [Cont, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod]
  rfl

theorem terminal_card : Nat.card (Cont Unit) = 4 := by
  simp only [Cont, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_unit]
  rfl

/-- Four common images, each with four independent choices for each of its two lifts. -/
theorem target_card :
    Nat.card (MappedPullback continuationMonad.toFunctor toUnit toUnit) = 64 := by
  rw [Nat.card_congr targetFibers,
    Nat.card_congr (Equiv.sigmaCongrRight (fun t => (fiberEquiv t).prodCongr (fiberEquiv t))),
    Nat.card_congr (Equiv.sigmaEquivProd _ _)]
  simp only [Cont, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_unit]
  rfl

theorem comparison_not_bijective :
    ¬ Function.Bijective (comparison continuationMonad.toFunctor toUnit toUnit) := by
  intro h
  have eq := Nat.card_congr (Equiv.ofBijective _ h)
  rw [source_card, target_card] at eq
  contradiction

/-- Even a mere natural representation of the underlying functor is ruled out. -/
theorem no_polynomial (E : Type) (D : E → Type) :
    ¬ Nonempty (continuationMonad.toFunctor ≅ polynomial E D) := by
  rintro ⟨e⟩
  exact comparison_not_bijective
    (comparison_bijective_of_iso e toUnit toUnit (polynomial_comparison_bijective E D _ _))

/-- The continuation monad has no pure-compatible discrete-grade presentation. -/
theorem no_presentation : ¬ Nonempty (Presentation (continuationMonad.{0})) := by
  rintro ⟨S⟩
  exact comparison_not_bijective (S.comparison_bijective toUnit toUnit)

end ContextualComposition.ContinuationTranspositionObstruction
