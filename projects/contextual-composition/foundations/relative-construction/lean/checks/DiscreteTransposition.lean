module

import ContextualComposition.ContinuationTranspositionObstruction

open CategoryTheory CategoryTheory.Limits
open ContextualComposition
open ContextualComposition.DiscreteTransposition
open ContextualComposition.ContinuationTranspositionObstruction

private abbrev I := CategoryTheory.Monad.id (Type 0)
private abbrev Shapes := polynomial Unit (fun _ => Unit)

/- This invertible chart for the identity monad at Bool flips the pointed value.
   Test a nonidentity pure map: constant true does not commute with the flip. -/
private def flipChart : MonadRecovery.Arrow I Unit Bool ≃ Shapes.obj Bool where
  toFun k := ⟨(), fun _ => !(k ())⟩
  invFun p := TypeCat.ofHom fun _ => !(p.2 ())
  left_inv k := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    exact Bool.not_not (k ())
  right_inv := by
    rintro ⟨⟨⟩, k⟩
    change (⟨(), fun _ => !(!(k ()))⟩ : Σ _ : Unit, Unit → Bool) = ⟨(), k⟩
    apply congrArg (Sigma.mk ())
    funext x
    cases x
    exact Bool.not_not (k ())

example :
    let k : MonadRecovery.Arrow I Unit Bool := TypeCat.ofHom fun _ => false
    let f : Bool ⟶ Bool := TypeCat.ofHom fun _ => true
    flipChart (MonadRecovery.comp I k (MonadRecovery.pure I f)) ≠
      Shapes.map f (flipChart k) := by
  intro k f h
  have h' := congrArg (fun x : Shapes.obj Bool => x.2 ()) h
  change false = true at h'
  cases h'

private abbrev Apex := Types.PullbackObj toUnit toUnit
private def point (b c : Bool) : Apex := ⟨(b, c), rfl⟩

/- The actual projections have different observable effects. An always-constant
   action or exchanged projection can have the same type, but not these outputs. -/
example :
    let k : Cont Apex := continuationMonad.η.app Apex (point false true)
    ((comparison continuationMonad.toFunctor toUnit toUnit k).1.1 id,
     (comparison continuationMonad.toFunctor toUnit toUnit k).1.2 id) =
      (false, true) := rfl

/- A pair in the ambient product can fail to lie in the actual target subtype. -/
example :
    ∀ q : MappedPullback continuationMonad.toFunctor toUnit toUnit,
      q.1 ≠ ((fun _ => false), (fun _ => true)) := by
  intro q h
  have test := congrFun q.2 (fun _ => false)
  obtain ⟨⟨k, l⟩, _⟩ := q
  change (k, l) = _ at h
  have hk : k = (fun _ => false) := congrArg Prod.fst h
  have hl : l = (fun _ => true) := congrArg Prod.snd h
  change k (fun _ => false) = l (fun _ => false) at test
  simp [hk, hl] at test

/- Collision on both actual projections, with a witness on a mixed predicate. -/
private def detectMixed (p : Apex → Bool) : Bool :=
  (p (point false false) != p (point false true)) &&
    (p (point false false) != p (point true false))

example : ¬ Function.Injective (comparison continuationMonad.toFunctor toUnit toUnit) := by
  intro inj
  have h : comparison continuationMonad.toFunctor toUnit toUnit detectMixed =
      comparison continuationMonad.toFunctor toUnit toUnit (fun _ => false) := by
    apply Subtype.ext
    apply Prod.ext
    · funext p
      change ((p false != p false) && (p false != p true)) = false
      cases p false <;> rfl
    · funext p
      change ((p false != p true) && (p false != p false)) = false
      cases p false <;> cases p true <;> rfl
  have h' := congrFun (inj h) (fun q => q.1.1 != q.1.2)
  change true = false at h'
  cases h'
