module
public import WitnessedDecompositions.Dynamic.Target
public import WitnessedDecompositions.PresentedCalculus
public import WitnessedDecompositions.SemanticRefinement
/-!
# Interpretation of the unchanged original syntax and presentations

A generator assignment consists of actual boundary-preserving graph maps. The
presentation premise is equality of the full interpreted graph maps, including
event records; the quotient is still the original least declared congruence.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WitnessedDecompositions.Dynamic.Assignment
open CategoryTheory
variable {V : Type u} [Quiver.{v} V] (D : Assignment.{u,v,w} V)
    (S : Signature.{u,v,z} V)

/-- Each original generator receives a graph map with its original full profile. -/
def GeneratorMaps := ∀ g : S.Generator,
  D.BoundaryMap (S.input g) (D.left (S.result g)) (D.right (S.result g))

def generatorEquiv : S.Assignment D.calculus ≃ D.GeneratorMaps S where
  toFun a g := D.operationEquiv (S.result g) (S.input g) (a g)
  invFun a g := (D.operationEquiv (S.result g) (S.input g)).symm (a g)
  left_inv a := by funext g; exact (D.operationEquiv _ _).symm_apply_apply (a g)
  right_inv a := by funext g; exact (D.operationEquiv _ _).apply_symm_apply (a g)

def assignment (a : D.GeneratorMaps S) : S.Assignment D.calculus :=
  (D.generatorEquiv S).symm a

/-- The actual original free-calculus extension into graph-span operations. -/
def freeExtend (a : D.GeneratorMaps S) : Calc.Hom (Tree.freeCalc S) D.calculus :=
  Tree.extend D.calculus (D.assignment S a)

/-- The original universal property specialized to all dynamic graph maps. -/
def freeHomEquiv : Calc.Hom (Tree.freeCalc S) D.calculus ≃ D.GeneratorMaps S :=
  (Tree.homEquiv D.calculus).trans (D.generatorEquiv S)

@[simp] theorem freeHomEquiv_symm (a : D.GeneratorMaps S) :
    (D.freeHomEquiv S).symm a = D.freeExtend S a := rfl

/-- The premise compares both state and actual event functions, not observations. -/
def EquationMaps (E : Presentation.Equations S) (a : D.GeneratorMaps S) : Prop :=
  ∀ c p (t u : Tree.Operation (S := S) c p), E c p t u →
    (D.operationEquiv c p (Tree.interpretFiber D.calculus (D.assignment S a) t)).val =
    (D.operationEquiv c p (Tree.interpretFiber D.calculus (D.assignment S a) u)).val

theorem equationMaps_iff_satisfies (E : Presentation.Equations S)
    (a : D.GeneratorMaps S) :
    D.EquationMaps S E a ↔ Presentation.Satisfies E D.calculus (D.assignment S a) := by
  constructor
  · intro h c p t u he
    apply (D.operationEquiv c p).injective
    exact Subtype.ext (h c p t u he)
  · intro h c p t u he
    exact congrArg (fun x => (D.operationEquiv c p x).val) (h c p t u he)

/-- No presentation model is manufactured without the actual equation premise. -/
def model (E : Presentation.Equations S) (a : D.GeneratorMaps S)
    (h : D.EquationMaps S E a) : Presentation.Model E D.calculus :=
  ⟨D.assignment S a, (D.equationMaps_iff_satisfies S E a).1 h⟩

noncomputable def presentedExtend (E : Presentation.Equations S)
    (a : D.GeneratorMaps S) (h : D.EquationMaps S E a) :
    Calc.Hom (Presentation.quotient E) D.calculus :=
  Presentation.extend E D.calculus (D.model S E a h)

@[simp] theorem projection_presentedExtend (E : Presentation.Equations S)
    (a : D.GeneratorMaps S) (h : D.EquationMaps S E a) :
    (Presentation.projection E).comp (D.presentedExtend S E a h) = D.freeExtend S a :=
  Presentation.projection_extend E D.calculus (D.model S E a h)

/-- Descent is equivalent to the stated full graph-map equation checks. -/
theorem descends_iff (E : Presentation.Equations S) (a : D.GeneratorMaps S) :
    (∃ F : Calc.Hom (Presentation.quotient E) D.calculus,
      (Presentation.projection E).comp F = D.freeExtend S a) ↔ D.EquationMaps S E a := by
  constructor
  · rintro ⟨F,hF⟩
    apply (D.equationMaps_iff_satisfies S E a).2
    have hs := Presentation.restrict_satisfies E D.calculus F
    rw [hF] at hs
    simpa only [freeExtend, Tree.restrict_extend] using hs
  · intro h
    exact ⟨D.presentedExtend S E a h, D.projection_presentedExtend S E a h⟩

/-- Retains one interpreted replacement per original occurrence in each arrow. -/
def freeRefinementFunctor (a : D.GeneratorMaps S) (c : Component V) :
    SemanticRefinement.Object (Tree.freeCalc S) c ⥤ SemanticRefinement.Object D.calculus c :=
  SemanticRefinement.functor (D.freeExtend S a) c

noncomputable def presentedRefinementFunctor (E : Presentation.Equations S)
    (a : D.GeneratorMaps S) (h : D.EquationMaps S E a) (c : Component V) :
    SemanticRefinement.Object (Presentation.quotient E) c ⥤
      SemanticRefinement.Object D.calculus c :=
  SemanticRefinement.functor (D.presentedExtend S E a h) c

end WitnessedDecompositions.Dynamic.Assignment
