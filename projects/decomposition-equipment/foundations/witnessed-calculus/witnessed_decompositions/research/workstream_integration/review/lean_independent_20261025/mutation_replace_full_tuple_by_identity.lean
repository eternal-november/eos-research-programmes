import RewriteFragmentCandidate

/-!
Checked concrete occurrence-forest normalization for the actual six-vertex,
three-interface graph-cut representative. Full standardized local cuts and
per-original-occurrence decorations are retained. This is a matched located
slice, connected to the public A3/B2 slice by the separately reviewed P adapter.
It does NOT assert that equality of substituted totals identifies forests.
-/
namespace IntegrationGraphForest
open GraphCoordinates TypedNormalizer RewriteFragmentCandidate

/-- A complete code at EACH original frontier occurrence. -/
def forestNormal {a b : Interface} (t : CutTerm a b) (F : FrontierForest t) :
    FrontierForest t := fun i => .leaf (frontierEntry t i).arrow (frontierEntry t i).block

def forestValid {a b : Interface} (t : CutTerm a b) (F : FrontierForest t) : Prop :=
  ∀ i, Valid (frontierEntry t i).block (F i)

theorem forestNormal_valid {a b : Interface} (t : CutTerm a b)
    (F : FrontierForest t) (hF : forestValid t F) : forestValid t (forestNormal t F) := by
  intro i
  exact (valid_congr _ (term_equiv_reify_normalize (F i))).mp (hF i)

theorem forestNormal_idempotent {a b : Interface} (t : CutTerm a b)
    (F : FrontierForest t) : forestNormal t (forestNormal t F) = forestNormal t F := by
  funext i
  exact congrArg reify (normalize_reify (F i).normalize)

theorem forestNormal_eq_iff_entry_equations {a b : Interface} (t : CutTerm a b)
    (F G : FrontierForest t) :
    forestNormal t F = forestNormal t G ↔ ∀ i, E (F i) (G i) := by
  constructor
  · intro h i
    apply (equiv_iff_normalize_eq _ _).mpr
    exact reify_injective (congrFun h i)
  · intro h
    funext i
    exact congrArg reify ((h i).sound)

/-- Actual canonical local coordinates, whole graphs, every ordered local leaf,
interface arrow and value are compared independently for every original slot. -/
theorem forestNormal_eq_iff_full_local_cuts {a b : Interface}
    (g : Graph) (t : CutTerm a b) (F G : FrontierForest t)
    (hF : forestValid t F) (hG : forestValid t G) :
    forestNormal t F = forestNormal t G ↔
      ∀ i, standardEvaluate g (frontierEntry t i).block (F i) =
        standardEvaluate g (frontierEntry t i).block (G i) := by
  rw [forestNormal_eq_iff_entry_equations]
  constructor
  · intro h i
    exact (equiv_iff_standard_cut_eq g _ _ _ (hF i) (hG i)).mp (h i)
  · intro h i
    exact (equiv_iff_standard_cut_eq g _ _ _ (hF i) (hG i)).mpr (h i)

/-- Pointwise equations need be supplied only at actual occurrences, not at
fictitious dispatch arguments. Units contribute no requirement. -/
theorem substitution_equations_at_leaves {a b : Interface} (t : CutTerm a b)
    (σ τ : Term.Substitution Block Decoration) (offset : Nat)
    (h : t.AllLeaves (fun n e => E (σ n e.arrow e.block) (τ n e.arrow e.block)) offset) :
    E (t.subst σ offset) (t.subst τ offset) := by
  induction t generalizing offset with
  | leaf hab x => exact h
  | unit a => exact E.refl _
  | cut s t ihs iht => exact E.cut (ihs _ h.1) (iht _ h.2)
  | deco m t ih => exact E.deco m (ih _ h)

/-- Derived mixed forest-entry compatibility for independently supplied
occurrence forests. The converse is intentionally absent and generally false. -/
theorem graft_entry_equations {a b : Interface} (t : CutTerm a b)
    (F G : FrontierForest t) (h : ∀ i, E (F i) (G i)) :
    E (t.subst (frontierDispatch t F) 0) (t.subst (frontierDispatch t G) 0) := by
  apply substitution_equations_at_leaves
  apply (Term.allLeaves_iff_entries _ _ 0).mpr
  intro i
  change E (frontierDispatch t F (0 + i.val) (frontierEntry t i).arrow
      (frontierEntry t i).block)
    (frontierDispatch t G (0 + i.val) (frontierEntry t i).arrow
      (frontierEntry t i).block)
  simpa only [Nat.zero_add, frontierDispatch_at] using h i

theorem graft_forest_normalization {a b : Interface} (t : CutTerm a b)
    (F : FrontierForest t) :
    E (t.subst (frontierDispatch t F) 0)
      (t.subst (frontierDispatch t (forestNormal t F)) 0) :=
  graft_entry_equations t F (forestNormal t F) (fun i => term_equiv_reify_normalize (F i))

theorem normalized_graft_valid {a b : Interface} {s : Block} (t : CutTerm a b)
    (ht : Valid s t) (F : FrontierForest t) (hF : forestValid t F) :
    Valid s (t.subst (frontierDispatch t (forestNormal t F)) 0) :=
  valid_frontierForest_graft t ht _ (forestNormal_valid t F hF)

/-- The two repeated nonempty component types in the accepted six-vertex model
may carry different LOCAL values even though their aggregated total cancels. -/
def decoratedMiddleLeft : CutTerm 1 1 := .deco 1 l1
def decoratedMiddleRight : CutTerm 1 1 := .deco 2 l2

def cancellingLocals : CutTerm 0 2 :=
  .cut l0 (.cut decoratedMiddleLeft (.cut decoratedMiddleRight l3))

theorem cancellingLocals_valid : Valid Finset.univ cancellingLocals := six_partition

theorem cancellingLocals_equal_total :
    E cancellingLocals rightBare := by
  apply (equiv_iff_normalize_eq _ _).mpr
  apply Prod.ext
  · rfl
  · decide

theorem first_local_value_not_erased :
    standardEvaluate sixGraph b1 decoratedMiddleLeft ≠ standardEvaluate sixGraph b1 l1 := by
  intro h
  have hd := congrArg (fun x : StandardCut b1 1 1 => x.decoration) h
  change (1 + 0 : Decoration) = 0 at hd
  norm_num at hd

/-- Nullary grafts retain scalar value even though their local frontier is empty. -/
def labelledNullary : CutTerm 1 1 := .deco 1 (.unit 1)

theorem labelledNullary_valid : Valid ∅ labelledNullary := valid_unit 1

theorem labelledNullary_has_no_occurrences : labelledNullary.frontier.entries = [] := rfl

theorem labelledNullary_not_identity_value :
    ¬ E labelledNullary (.unit 1 : CutTerm 1 1) := by
  intro h
  have hw := congrArg Prod.snd h.sound
  change (1 + 0 : Decoration) = 0 at hw
  norm_num at hw

theorem decorated_unit_moves_without_loss :
    E (.cut labelledNullary l1) (.deco 1 l1) :=
  E.trans (E.DL 1 (.unit 1) l1) (E.deco 1 (E.UL l1))

/-- A local binary refinement changes that entry's full profile; keeping only
the global resulting operation is not a forest equality certificate. -/
theorem repeated_local_profiles_differ :
    splitFirstMiddle.frontier.length ≠ l1.frontier.length := by decide

/-- Identity replacement at each actual slot, independently indexed. -/
def identityForest {a b : Interface} (t : CutTerm a b) : FrontierForest t :=
  fun i => .leaf (frontierEntry t i).arrow (frontierEntry t i).block

/-- Actual four-entry forest: the two equal component colours receive values
1 and 2 separately; neither value is recovered from its component name. -/
def cancellingForest : FrontierForest rightBare := fun i =>
  if i.val = 1 then .deco 1 (identityForest rightBare i)
  else if i.val = 2 then .deco 2 (identityForest rightBare i)
  else identityForest rightBare i

theorem cancellingForest_valid : forestValid rightBare cancellingForest := by
  intro i
  fin_cases i <;> exact valid_leaf _ _

theorem identityForest_valid {a b : Interface} (t : CutTerm a b) :
    forestValid t (identityForest t) := fun _i => valid_leaf _ _

theorem cancellingForest_actual_graft :
    rightBare.subst (frontierDispatch rightBare cancellingForest) 0 = cancellingLocals := by
  rfl

theorem identityForest_actual_graft :
    rightBare.subst (frontierDispatch rightBare (identityForest rightBare)) 0 = rightBare := by
  rfl

/-- Genuine nonthin-arrow phenomenon at the level of independent full tuple
codes: equal composite operation, but different original-slot normal forms. -/
theorem equal_grafts_unequal_forest_codes :
    E (rightBare.subst (frontierDispatch rightBare cancellingForest) 0)
      (rightBare.subst (frontierDispatch rightBare (identityForest rightBare)) 0) ∧
    forestNormal rightBare cancellingForest ≠
      forestNormal rightBare (identityForest rightBare) := by
  constructor
  · rw [cancellingForest_actual_graft, identityForest_actual_graft]
    exact cancellingLocals_equal_total
  · intro he
    have hi := (forestNormal_eq_iff_entry_equations rightBare _ _).mp he ⟨1, by decide⟩
    exact first_local_value_not_erased (evaluate_standard hi)
where
  evaluate_standard {x y : CutTerm 1 1} (h : E x y) :
      standardEvaluate sixGraph b1 x = standardEvaluate sixGraph b1 y := by
    have hf := h.frontier_eq
    have hw := congrArg Prod.snd h.sound
    change x.weight = y.weight at hw
    simp only [standardEvaluate, hf, hw]

end IntegrationGraphForest
