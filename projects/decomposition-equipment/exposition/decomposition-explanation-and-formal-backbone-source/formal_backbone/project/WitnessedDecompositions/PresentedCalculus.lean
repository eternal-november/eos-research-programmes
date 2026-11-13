module

public import WitnessedDecompositions.QuotientCalculus

/-!
# Presented universal property and all-model completeness

The quotient is by the least declared parallel congruence, not by the kernel of
one selected semantics. Standard choice is used only by the generic quotient's
representative implementation; no normalization or decidability is inferred.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z z'
namespace WitnessedDecompositions.Presentation
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- The calculus presented by exactly the declared equations and their least closure. -/
noncomputable def quotient (E : Equations S) : Calc.{u, v, max u v w} V :=
  (congruence E).quotient

/-- The strict quotient projection retains every ordered profile. -/
noncomputable def projection (E : Equations S) : Calc.Hom (Tree.freeCalc S) (quotient E) :=
  (congruence E).projection

/-- Derivability is exactly equality in the actual quotient calculus. -/
theorem quotient_eq_iff (E : Equations S) {c : Component V} (t u : Tree S c) :
    (projection E).map t = (projection E).map u ↔ Derives S E t u :=
  (congruence E).quotient_eq_iff t u

/-- A model of the presentation is an arbitrary well-typed primitive assignment satisfying E. -/
def Model (E : Equations S) (M : Calc.{u, v, z} V) :=
  {a : S.Assignment M // Satisfies E M a}

/-- Soundness supplies exactly the relation-respect needed for quotient factorization. -/
theorem extend_respects (E : Equations S) (M : Calc.{u, v, z} V)
    (a : Model E M) : (congruence E).Respects (Tree.extend M a.val) :=
  fun h => sound E M a.val a.property h

/-- The unique descended strict interpretation of any presentation model. -/
noncomputable def extend (E : Equations S) (M : Calc.{u, v, z} V)
    (a : Model E M) : Calc.Hom (quotient E) M :=
  (congruence E).factor (Tree.extend M a.val) (extend_respects E M a)

/-- Composing the descended interpretation with projection is the original free extension. -/
@[simp] theorem projection_extend (E : Equations S) (M : Calc.{u, v, z} V)
    (a : Model E M) : (projection E).comp (extend E M a) = Tree.extend M a.val :=
  (congruence E).projection_factor _ _

/-- An assignment obtained by restricting a strict map is evaluated by that map. -/
theorem interpret_restrict (M : Calc.{u, v, z} V)
    (F : Calc.Hom (Tree.freeCalc S) M) {c : Component V} (t : Tree S c) :
    Tree.interpret M (Tree.restrict M F) t = F.map t :=
  congrArg (fun H : Calc.Hom (Tree.freeCalc S) M => H.map t) (Tree.extend_restrict M F)

/-- Every strict map out of the quotient yields a model of all declared equations. -/
theorem restrict_satisfies (E : Equations S) (M : Calc.{u, v, z} V)
    (F : Calc.Hom (quotient E) M) : Satisfies E M (Tree.restrict M ((projection E).comp F)) := by
  intro c p t u he
  apply Subtype.ext
  change Tree.interpret M (Tree.restrict M ((projection E).comp F)) t.val =
    Tree.interpret M (Tree.restrict M ((projection E).comp F)) u.val
  rw [interpret_restrict, interpret_restrict]
  exact congrArg F.map ((quotient_eq_iff E t.val u.val).2 (Derives.equation t u he))

/-- Restrict a strict quotient interpretation to its primitive presentation model. -/
noncomputable def restrict (E : Equations S) (M : Calc.{u, v, z} V)
    (F : Calc.Hom (quotient E) M) : Model E M :=
  ⟨Tree.restrict M ((projection E).comp F), restrict_satisfies E M F⟩

/-- The quotient projection is an epimorphism on actual strict maps. -/
theorem projection_ext (E : Equations S) {M : Calc.{u, v, z} V}
    {F G : Calc.Hom (quotient E) M}
    (h : (projection E).comp F = (projection E).comp G) : F = G := by
  apply Calc.Hom.ext
  intro c a
  induction a using Quotient.inductionOn with
  | _ a => exact congrArg (fun H : Calc.Hom (Tree.freeCalc S) M => H.map a) h

@[simp] theorem restrict_extend (E : Equations S) (M : Calc.{u, v, z} V)
    (a : Model E M) : restrict E M (extend E M a) = a := by
  apply Subtype.ext
  change Tree.restrict M ((projection E).comp (extend E M a)) = a.val
  rw [projection_extend, Tree.restrict_extend]

@[simp] theorem extend_restrict (E : Equations S) (M : Calc.{u, v, z} V)
    (F : Calc.Hom (quotient E) M) : extend E M (restrict E M F) = F := by
  apply projection_ext E
  rw [projection_extend]
  exact Tree.extend_restrict M ((projection E).comp F)

/-- The presented universal property, with mutually inverse maps for every target. -/
noncomputable def homEquiv (E : Equations S) (M : Calc.{u, v, z} V) :
    Calc.Hom (quotient E) M ≃ Model E M where
  toFun := restrict E M
  invFun := extend E M
  left_inv := extend_restrict E M
  right_inv := restrict_extend E M

/-- Uniqueness among every strict factor, not merely a chosen recursive evaluation. -/
theorem extend_unique (E : Equations S) (M : Calc.{u, v, z} V) (a : Model E M)
    (F : Calc.Hom (quotient E) M)
    (h : (projection E).comp F = Tree.extend M a.val) : F = extend E M a := by
  apply projection_ext E
  exact h.trans (projection_extend E M a).symm

/-- Models are closed under arbitrary strict postcomposition. -/
def postcomposeModel (E : Equations S) {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (a : Model E M) (k : Calc.Hom M N) : Model E N :=
  ⟨(fun g => k.onOperation (a.val g)), by
    intro c p t u he
    apply Subtype.ext
    have hn := Tree.extend_natural_target a.val k
    have ht := congrArg (fun F : Calc.Hom (Tree.freeCalc S) N => F.map t.val) hn
    have hu := congrArg (fun F : Calc.Hom (Tree.freeCalc S) N => F.map u.val) hn
    exact ht.symm.trans ((congrArg k.map (congrArg Subtype.val (a.property c p t u he))).trans hu)⟩

/-- Presented extension is natural in every target calculus, across universes. -/
theorem extend_natural (E : Equations S) {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (a : Model E M) (k : Calc.Hom M N) :
    (extend E M a).comp k = extend E N (postcomposeModel E a k) := by
  apply projection_ext E
  rw [← Calc.Hom.comp_assoc, projection_extend, projection_extend]
  exact Tree.extend_natural_target a.val k

/-- The presented calculus itself is a model of its defining equations. -/
noncomputable def canonicalModel (E : Equations S) : Model E (quotient E) :=
  restrict E (quotient E) (Calc.Hom.id (quotient E))

@[simp] theorem interpret_canonical (E : Equations S) {c : Component V} (t : Tree S c) :
    Tree.interpret (quotient E) (canonicalModel E).val t = (projection E).map t :=
  interpret_restrict (quotient E) ((projection E).comp (Calc.Hom.id (quotient E))) t

/-- All models in a specified universe large enough to contain the presented calculus.
Soundness into targets in every other universe is separately theorem `sound`. -/
def EqualInAllModels (E : Equations S) {c : Component V} (t u : Tree S c) : Prop :=
  ∀ (M : Calc.{u, v, max u v w} V) (a : Model E M),
    Tree.interpret M a.val t = Tree.interpret M a.val u

/-- Completeness uses the actual presented calculus as a separating model. -/
theorem derives_iff_all_models (E : Equations S) {c : Component V} (t u : Tree S c) :
    Derives S E t u ↔ EqualInAllModels E t u := by
  constructor
  · intro h M a
    exact sound E M a.val a.property h
  · intro h
    apply (quotient_eq_iff E t u).1
    have hm := h (quotient E) (canonicalModel E)
    simpa only [interpret_canonical] using hm

/-- Equality in one model need not be derivability; the theorem requires EVERY model. -/
theorem quotient_eq_iff_all_models (E : Equations S) {c : Component V} (t u : Tree S c) :
    (projection E).map t = (projection E).map u ↔ EqualInAllModels E t u :=
  (quotient_eq_iff E t u).trans (derives_iff_all_models E t u)

end WitnessedDecompositions.Presentation
