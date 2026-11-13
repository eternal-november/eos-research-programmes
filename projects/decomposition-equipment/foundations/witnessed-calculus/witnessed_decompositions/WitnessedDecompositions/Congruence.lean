module

public import WitnessedDecompositions.FreeExtension

/-!
# Least parallel substitution congruences

Declared equations inhabit a common full profile fibre. The closure contains
only equivalence rules and simultaneous occurrence-wise substitution; equality
in an arbitrarily selected semantic model is not a generation rule.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z z'

namespace WitnessedDecompositions

/-- A substitution-stable equivalence relation whose related operations are parallel. -/
structure ParallelCongruence {V : Type u} [Quiver.{v} V] (M : Calc.{u, v, z} V) where
  Rel : ∀ {c : Component V}, M.Op c → M.Op c → Prop
  refl : ∀ {c} (a : M.Op c), Rel a a
  symm : ∀ {c} {a b : M.Op c}, Rel a b → Rel b a
  trans : ∀ {c} {a b d : M.Op c}, Rel a b → Rel b d → Rel a d
  parallel : ∀ {c} {a b : M.Op c}, Rel a b → M.profile a = M.profile b
  substitute : ∀ {c : Component V} {p : Quiver.Path c.source c.target}
    (a b : M.Operation c p), Rel a.val b.val →
    ∀ (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
      (f g : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i)),
      (∀ i, Rel (f i).val (g i).val) → Rel (M.substitute a q f).val (M.substitute b q g).val

namespace ParallelCongruence

variable {V : Type u} [Quiver.{v} V] {M : Calc.{u, v, z} V}

/-- The equivalence relation at each output component. -/
def setoid (R : ParallelCongruence M) (c : Component V) : Setoid (M.Op c) where
  r := R.Rel
  iseqv := ⟨R.refl, R.symm, R.trans⟩

/-- Kernels of strict maps are parallel congruences, not declarations of equations. -/
def kernel {N : Calc.{u, v, z'} V} (F : Calc.Hom M N) : ParallelCongruence M where
  Rel a b := F.map a = F.map b
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans
  parallel {c} {a b} h := (F.profile_map a).symm.trans
    ((congrArg N.profile h).trans (F.profile_map b))
  substitute a b hab q f g hfg := by
    have hOuter : F.onOperation a = F.onOperation b := Subtype.ext hab
    have hInner : (fun i => F.onOperation (f i)) = (fun i => F.onOperation (g i)) := by
      funext i
      exact Subtype.ext (hfg i)
    change (F.onOperation (M.substitute a q f)).val = (F.onOperation (M.substitute b q g)).val
    rw [F.onOperation_substitute, F.onOperation_substitute, hOuter, hInner]

end ParallelCongruence

namespace Presentation

variable {V : Type u} [Quiver.{v} V] (S : Signature.{u, v, w} V)

/-- Arbitrary declared equations, with parallelism enforced before a clause can be stated. -/
def Equations := ∀ (c : Component V) (p : Quiver.Path c.source c.target),
  Tree.Operation (S := S) c p → Tree.Operation (S := S) c p → Prop

/-- The least equivalence closed under all well-typed simultaneous substitutions. -/
inductive Derives (E : Equations S) : {c : Component V} → Tree S c → Tree S c → Prop where
  | equation {c : Component V} {p : Quiver.Path c.source c.target}
      (a b : Tree.Operation (S := S) c p) : E c p a b → Derives E a.val b.val
  | refl {c : Component V} (a : Tree S c) : Derives E a a
  | symm {c : Component V} {a b : Tree S c} : Derives E a b → Derives E b a
  | trans {c : Component V} {a b d : Tree S c} :
      Derives E a b → Derives E b d → Derives E a d
  | substitute {c : Component V} {p : Quiver.Path c.source c.target}
      (a b : Tree.Operation (S := S) c p) : Derives E a.val b.val →
      ∀ (q : ∀ i : Path.Slot p,
        Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
        (f g : ∀ i : Path.Slot p, Tree.Operation (S := S) (Path.componentAt p i) (q i)),
        (∀ i, Derives E (f i).val (g i).val) →
        Derives E (Tree.substituteOperation a q f).val (Tree.substituteOperation b q g).val

variable {S} (E : Equations S)

/-- Derivability never changes endpoints, intermediate interfaces, order, or the frontier. -/
theorem derives_parallel {c : Component V} {a b : Tree S c} (h : Derives S E a b) :
    Tree.frontier a = Tree.frontier b := by
  induction h with
  | equation a b _ => exact a.property.trans b.property.symm
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | substitute a b _ q f g _ _ _ =>
      exact (Tree.substituteOperation a q f).property.trans
        (Tree.substituteOperation b q g).property.symm

/-- The inductive closure actually is a parallel substitution congruence. -/
def congruence : ParallelCongruence (Tree.freeCalc S) where
  Rel := Derives S E
  refl := Derives.refl
  symm := Derives.symm
  trans := Derives.trans
  parallel := derives_parallel E
  substitute := Derives.substitute

/-- Leastness, quantified over every parallel substitution congruence. -/
theorem derives_least (R : ParallelCongruence (Tree.freeCalc S))
    (hE : ∀ c p (a b : Tree.Operation (S := S) c p), E c p a b → R.Rel a.val b.val)
    {c : Component V} {a b : Tree S c} (h : Derives S E a b) : R.Rel a b := by
  induction h with
  | equation a b h => exact hE _ _ a b h
  | refl a => exact R.refl a
  | symm _ ih => exact R.symm ih
  | trans _ _ ih₁ ih₂ => exact R.trans ih₁ ih₂
  | substitute a b _ q f g _ ih ihfg => exact R.substitute a b ih q f g ihfg

/-- A primitive assignment satisfies exactly the declared equations. -/
def Satisfies (M : Calc.{u, v, z} V) (a : S.Assignment M) : Prop :=
  ∀ c p (t u : Tree.Operation (S := S) c p), E c p t u →
    Tree.interpretFiber M a t = Tree.interpretFiber M a u

/-- Every model of the declared presentation respects its least congruence. -/
theorem sound (M : Calc.{u, v, z} V) (a : S.Assignment M) (hE : Satisfies E M a)
    {c : Component V} {t u : Tree S c} (h : Derives S E t u) :
    Tree.interpret M a t = Tree.interpret M a u := by
  apply derives_least E (ParallelCongruence.kernel (Tree.extend M a)) ?_ h
  intro c p t u he
  exact congrArg Subtype.val (hE c p t u he)

end Presentation
end WitnessedDecompositions
