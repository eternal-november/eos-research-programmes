module
public import ContextualComposition.PositiveHistoryComposition

/-! Coherence of the forward comparison from composed support samplers
to the support sampler of the composed kernel. The source always retains
the actual intermediate samples. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.PositiveSamplerCoherence
open CategoryTheory PositiveHistoryReflection PositiveHistoryComposition FiniteProbabilityLaws FiniteProbabilityMonad IndependentProbabilityProduct
set_option backward.isDefEq.respectTransparency false
universe u
variable {A B C D : Type u}

def pairMap {P P' : Positive A B} {Q Q' : Positive B C}
    (f : P ⟶ P') (g : Q ⟶ Q') (a : A) (z : (compose P Q).history.witness a) :
    (compose P' Q').history.witness a :=
  ⟨f.run a z.1,(f.output a z.1).symm ▸ g.run _ z.2⟩

theorem pairMap_output {P P' : Positive A B} {Q Q' : Positive B C}
    (f : P ⟶ P') (g : Q ⟶ Q') (a : A) (z : (compose P Q).history.witness a) :
    (compose P' Q').history.output a (pairMap f g a z) = (compose P Q).history.output a z := by
  have transport (b b' : B) (h : b = b') (y : Q'.history.witness b) :
      Q'.history.output b' (h ▸ y) = Q'.history.output b y := by cases h; rfl
  exact (transport _ _ (f.output a z.1).symm _).trans (g.output _ _)

def horizontal {P P' : Positive A B} {Q Q' : Positive B C} (f : P ⟶ P') (g : Q ⟶ Q') :
    compose P Q ⟶ compose P' Q' := by
  refine ⟨pairMap f g,?_,pairMap_output f g⟩
  intro a
  let _ := P.history.finite
  let _ := P'.history.finite
  let _ := Q.history.finite
  let _ := Q'.history.finite
  apply expect_ext
  intro h
  rw [expect_image]
  erw [dependent_expect, dependent_expect, ← f.preserves a, expect_image]
  apply expect_congr
  intro x
  let y := P'.history.output a (f.run a x)
  let k := f.output a x
  have transport (b : B) (eq : P.history.output a x = b)
      (t : Q'.history.witness b → ℝ) :
      expect (Q.history.weights (P.history.output a x)) (fun z => t (eq ▸ g.run _ z)) =
        expect (Q'.history.weights b) t := by
    cases eq
    rw [← g.preserves,expect_image]
    rfl
  exact transport y k.symm (fun z => h ⟨f.run a x,z⟩)

def assocMap (P : Positive A B) (Q : Positive B C) (R : Positive C D) :
    compose (compose P Q) R ⟶ compose P (compose Q R) := by
  refine ⟨fun _ z => ⟨z.1.1,z.1.2,z.2⟩,?_,fun _ _ => rfl⟩
  intro a
  let _ := P.history.finite
  let _ := Q.history.finite
  let _ := R.history.finite
  let _ := (compose P Q).history.finite
  let _ := (compose Q R).history.finite
  apply expect_ext
  intro h
  rw [expect_image]
  erw [dependent_expect,dependent_expect,dependent_expect]
  apply expect_congr
  intro x
  exact (dependent_expect (Q.history.weights (P.history.output a x))
    (fun y => R.history.witness (Q.history.output (P.history.output a x) y))
    (fun y => R.history.weights (Q.history.output (P.history.output a x) y)) (fun z => h ⟨x,z⟩)).symm

def unassocMap (P : Positive A B) (Q : Positive B C) (R : Positive C D) :
    compose P (compose Q R) ⟶ compose (compose P Q) R := by
  refine ⟨fun _ z => ⟨⟨z.1,z.2.1⟩,z.2.2⟩,?_,fun _ _ => rfl⟩
  intro a
  let _ := P.history.finite
  let _ := Q.history.finite
  let _ := R.history.finite
  let _ := (compose P Q).history.finite
  let _ := (compose Q R).history.finite
  apply expect_ext
  intro h
  rw [expect_image]
  erw [dependent_expect,dependent_expect,dependent_expect]
  apply expect_congr
  intro x
  exact dependent_expect (Q.history.weights _) _ _ _

def associator (P : Positive A B) (Q : Positive B C) (R : Positive C D) :
    compose (compose P Q) R ≅ compose P (compose Q R) :=
  ⟨assocMap P Q R,unassocMap P Q R,Map.ext rfl,Map.ext rfl⟩

theorem kernel_assoc (k : A → Law B) (l : B → Law C) (m : C → Law D) :
    kernelComp (kernelComp k l) m = kernelComp k (kernelComp l m) := by
  funext a
  apply expect_ext
  intro h
  simp [kernelComp,expect_mixture]

theorem associativity (k : A → Law B) (l : B → Law C) (m : C → Law D) :
    horizontal (samplerComparison k l) (𝟙 (support m)) ≫ samplerComparison (kernelComp k l) m =
      (associator (support k) (support l) (support m)).hom ≫
        horizontal (𝟙 (support k)) (samplerComparison l m) ≫ samplerComparison k (kernelComp l m) ≫
        eqToHom (congrArg support (kernel_assoc k l m).symm) := unique_to_support _ _ _ _

def unitHistory (A : Type u) : Positive A A where
  history := ⟨fun _ => PUnit,fun _ => inferInstance,fun _ => dirac PUnit.unit,fun a _ => a⟩
  positive _ x := by cases x; simp [dirac]

theorem kernel_unit (A : Type u) : kernel (unitHistory A).history = dirac := by
  funext a; apply expect_ext; intro h
  change expect (image (fun _ : PUnit => a) (dirac PUnit.unit)) _ = _
  rw [expect_image,expect_dirac,expect_dirac]; rfl

def unitComparison (A : Type u) : unitHistory A ⟶ support dirac := toSupport _ _ (kernel_unit A)

theorem support_dirac_value (a : A) (x : Supported (dirac a)) : x.val = a := by
  classical
  have h := x.property
  simpa [dirac] using h

def unitIso (A : Type u) : unitHistory A ≅ support dirac where
  hom := unitComparison A
  inv := {
    run := fun _ _ => PUnit.unit
    preserves := by
      intro a; apply expect_ext; intro h
      rw [expect_image]
      exact (expect_const _ _).trans (expect_dirac _ _).symm
    output := fun a x => (support_dirac_value a x).symm }
  hom_inv_id := by apply Map.ext; funext a x; exact Subsingleton.elim (α := PUnit) _ _
  inv_hom_id := unique_to_support _ _ _ _

theorem kernel_left (k : A → Law B) : kernelComp dirac k = k := by
  funext a; apply expect_ext; intro h
  simp [kernelComp,expect_mixture,expect_dirac]

theorem kernel_right (k : A → Law B) : kernelComp k dirac = k := by
  funext a; apply expect_ext; intro h
  simp [kernelComp,expect_mixture,expect_dirac]

def leftUnit (P : Positive A B) : compose (unitHistory A) P ⟶ P := by
  refine ⟨fun _ z => z.2,?_,fun _ _ => rfl⟩
  intro a
  let _ := (unitHistory A).history.finite
  let _ := P.history.finite
  apply expect_ext; intro h
  rw [expect_image]; erw [dependent_expect,expect_dirac]; rfl

def rightUnit (P : Positive A B) : compose P (unitHistory B) ⟶ P := by
  refine ⟨fun _ z => z.1,?_,fun _ _ => rfl⟩
  intro a
  let _ := P.history.finite
  let _ := (unitHistory B).history.finite
  apply expect_ext; intro h
  rw [expect_image]; erw [dependent_expect]; apply expect_congr; intro x
  exact expect_dirac _ _

theorem left_law (k : A → Law B) :
    horizontal (unitComparison A) (𝟙 (support k)) ≫ samplerComparison dirac k ≫
      eqToHom (congrArg support (kernel_left k)) = leftUnit (support k) := unique_to_support _ _ _ _

theorem right_law (k : A → Law B) :
    horizontal (𝟙 (support k)) (unitComparison B) ≫ samplerComparison k dirac ≫
      eqToHom (congrArg support (kernel_right k)) = rightUnit (support k) := unique_to_support _ _ _ _

theorem pentagon {E : Type u} (P : Positive A B) (Q : Positive B C) (R : Positive C D) (S : Positive D E) :
    horizontal (associator P Q R).hom (𝟙 S) ≫ (associator P (compose Q R) S).hom ≫
      horizontal (𝟙 P) (associator Q R S).hom =
      (associator (compose P Q) R S).hom ≫ (associator P Q (compose R S)).hom := Map.ext rfl

theorem triangle (P : Positive A B) (Q : Positive B C) :
    (associator P (unitHistory B) Q).hom ≫ horizontal (𝟙 P) (leftUnit Q) =
      horizontal (rightUnit P) (𝟙 Q) := Map.ext rfl

end ContextualComposition.PositiveSamplerCoherence
