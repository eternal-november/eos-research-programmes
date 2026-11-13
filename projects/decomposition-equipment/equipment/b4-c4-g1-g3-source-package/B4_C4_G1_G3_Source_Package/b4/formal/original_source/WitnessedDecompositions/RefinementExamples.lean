module

public import WitnessedDecompositions.PresentationExamples
public import WitnessedDecompositions.RawRefinement
public import WitnessedDecompositions.SemanticRefinement

/-!
B2 certificate: a genuinely many-interface associative presentation with retained
unary witnesses. Contract v0.1, SHA256
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
No equation is imposed on the raw syntax. All quotient equalities below use
Presentation.Derives and the actual accepted A3 quotient.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
namespace WitnessedDecompositions.RefinementExamples
open Tree

/-- There are genuinely distinct interfaces, with one named directed component
between each ordered pair. Repeated loop occurrences remain independent slots. -/
instance : Quiver Nat := ⟨fun _ _ => Unit⟩

def component (a b : Nat) : Component Nat := ⟨a, b, ()⟩
def pairPath (a b c : Nat) : Quiver.Path a c :=
  (Quiver.Path.nil.cons (show a ⟶ b from ())).cons (show b ⟶ c from ())
def triplePath (a b c d : Nat) : Quiver.Path a d :=
  (pairPath a b c).cons (show c ⟶ d from ())

inductive Gen where
  | binary (a b c : Nat)
  | red (a b : Nat)
  | blue (a b : Nat)
  | zero (a : Nat)
  deriving DecidableEq

def S : Signature Nat where
  Generator := Gen
  source
    | .binary a _ _ | .red a _ | .blue a _ | .zero a => a
  target
    | .binary _ _ c | .red _ c | .blue _ c | .zero c => c
  input
    | .binary a b c => pairPath a b c
    | .red a b | .blue a b => (component a b).edge.toPath
    | .zero a => Quiver.Path.nil (a := a)
  output
    | .binary _ _ _ | .red _ _ | .blue _ _ | .zero _ => ()

/-- Binary composition is syntax, not an assumed associative operation. -/
def join (a b c : Nat) (t : Tree S (component a b))
    (u : Tree S (component b c)) : Tree S (component a c) :=
  .node (S := S) (Gen.binary a b c) (Examples.binaryChildren t u)

def mu (a b c : Nat) : Tree S (component a c) :=
  corolla (S := S) (Gen.binary a b c)

def assocLeft (a b c d : Nat) : Tree S (component a d) :=
  join a c d (mu a b c) (.leaf (component c d))
def assocRight (a b c d : Nat) : Tree S (component a d) :=
  join a b d (.leaf (component a b)) (mu b c d)

def assocLeftOp (a b c d : Nat) : Operation (S := S) (component a d)
    (triplePath a b c d) := ⟨assocLeft a b c d, rfl⟩
def assocRightOp (a b c d : Nat) : Operation (S := S) (component a d)
    (triplePath a b c d) := ⟨assocRight a b c d, rfl⟩

/-- An unbounded, explicitly indexed schema, not a single hand-equated pair.
Arbitrary substitution closure is supplied by Presentation.Derives. -/
inductive Declared : ∀ (c : Component Nat) (p : Quiver.Path c.source c.target),
    Operation (S := S) c p → Operation (S := S) c p → Prop where
  | associativity (a b c d : Nat) :
      Declared (component a d) (triplePath a b c d)
        (assocLeftOp a b c d) (assocRightOp a b c d)

def equations : Presentation.Equations S := Declared

noncomputable def M : Calc Nat := Presentation.quotient equations
noncomputable def projection : Calc.Hom (freeCalc S) M := Presentation.projection equations

 theorem associativity_derivable (a b c d : Nat) :
    Presentation.Derives S equations (assocLeft a b c d) (assocRight a b c d) :=
  Presentation.Derives.equation _ _ (Declared.associativity a b c d)

 theorem associativity_evaluated (a b c d : Nat) :
    projection.map (assocLeft a b c d) = projection.map (assocRight a b c d) :=
  (Presentation.quotient_eq_iff equations _ _).2 (associativity_derivable a b c d)

/-- Leaves must be retained in a shape discriminator: the two binary groupings
have the same preorder generator list in the repeated-loop instance. -/
inductive Shape where
  | leaf
  | node (children : List Shape)

def shape : {c : Component Nat} → Tree S c → Shape
  | _, .leaf _ => .leaf
  | _, .node g children => .node (Path.collect (S.input g) (fun i => [shape (children i)]))

 theorem groupings_distinct (a b c d : Nat) : assocLeft a b c d ≠ assocRight a b c d := by
  intro h
  have hs := congrArg shape h
  change Shape.node [Shape.node [.leaf, .leaf], .leaf] =
    Shape.node [.leaf, Shape.node [.leaf, .leaf]] at hs
  cases hs

def red (a b : Nat) : Tree S (component a b) := corolla (S := S) (.red a b)
def blue (a b : Nat) : Tree S (component a b) := corolla (S := S) (.blue a b)
def zero (a : Nat) : Tree S (component a a) := corolla (S := S) (.zero a)

def redWeight : Gen → Nat
  | .red _ _ => 1
  | _ => 0

 theorem declarations_preserve_red : ∀ c p (a b : Operation (S := S) c p),
    equations c p a b → weight redWeight a.val = weight redWeight b.val := by
  intro c p a b h
  cases h
  rfl

 theorem red_blue_distinct_in_quotient (a b : Nat) :
    projection.map (red a b) ≠ projection.map (blue a b) := by
  intro h
  have hd := (Presentation.quotient_eq_iff equations _ _).1 h
  have hw := Presentation.derives_weight equations redWeight declarations_preserve_red hd
  change 1 = 0 at hw
  cases hw

 theorem quotient_retains_red_count {c : Component Nat} {t u : Tree S c}
    (h : projection.map t = projection.map u) : weight redWeight t = weight redWeight u :=
  Presentation.derives_weight equations redWeight declarations_preserve_red
    ((Presentation.quotient_eq_iff equations _ _).1 h)

/-- The relevant repeated component is literally the same typed loop. -/
def x : Component Nat := component 1 1
def root : Tree S x := mu 1 1 1
def left : Tree S x := assocLeft 1 1 1 1
def right : Tree S x := assocRight 1 1 1 1

 theorem loop_groupings_distinct : left ≠ right := groupings_distinct 1 1 1 1
 theorem loop_groupings_equal_in_quotient : projection.map left = projection.map right :=
  associativity_evaluated 1 1 1 1

/-- A typed context with interfaces 0,1,2, preserving the two separate loop slots. -/
def context (t : Tree S x) : Tree S (component 0 2) :=
  join 0 1 2 (.leaf (component 0 1))
    (join 1 1 2 t (.leaf (component 1 2)))

def mixedSource : Tree S (component 0 2) := context root
def mixedLeft : Tree S (component 0 2) := context left
def mixedRight : Tree S (component 0 2) := context right

def mixedSourcePath : Quiver.Path (V := Nat) 0 2 :=
  (((Quiver.Path.nil.cons (show 0 ⟶ 1 from ())).cons (show 1 ⟶ 1 from ())).cons
    (show 1 ⟶ 1 from ())).cons (show 1 ⟶ 2 from ())
def mixedTargetPath : Quiver.Path (V := Nat) 0 2 :=
  ((((Quiver.Path.nil.cons (show 0 ⟶ 1 from ())).cons (show 1 ⟶ 1 from ())).cons
    (show 1 ⟶ 1 from ())).cons (show 1 ⟶ 1 from ())).cons (show 1 ⟶ 2 from ())

 theorem mixed_source_frontier : frontier mixedSource = mixedSourcePath := rfl
 theorem mixed_left_frontier : frontier mixedLeft = mixedTargetPath := rfl
 theorem mixed_right_frontier : frontier mixedRight = mixedTargetPath := rfl
 theorem mixed_source_four_leaves : (frontier mixedSource).length = 4 := rfl
 theorem mixed_target_five_leaves : (frontier mixedLeft).length = 5 := rfl
 theorem mixed_source_components : leaves mixedSource =
    [component 0 1, x, x, component 1 2] := rfl
 theorem mixed_target_components : leaves mixedLeft =
    [component 0 1, x, x, x, component 1 2] := rfl
 theorem mixed_groupings_distinct : mixedLeft ≠ mixedRight := by
  intro h
  have hs := congrArg shape h
  change Shape.node [.leaf, .node [.node [.node [.leaf, .leaf], .leaf], .leaf]] =
    Shape.node [.leaf, .node [.node [.leaf, .node [.leaf, .leaf]], .leaf]] at hs
  cases hs


/-- Two independently supplied replacement families at the two identical slots. -/
def leftFamily : (collection S).Family (frontier root) :=
  Examples.binaryChildren root (.leaf x)
def rightFamily : (collection S).Family (frontier root) :=
  Examples.binaryChildren (.leaf x) root

theorem graft_mu (a b c : Nat) (t : Tree S (component a b))
    (u : Tree S (component b c)) :
    profileGraft (mu a b c) (Examples.binaryChildren t u) = join a b c t u :=
  profileGraft_corolla (S := S) (Gen.binary a b c) (Examples.binaryChildren t u)

theorem graft_leftFamily : profileGraft root leftFamily = left := graft_mu 1 1 1 _ _
theorem graft_rightFamily : profileGraft root rightFamily = right := graft_mu 1 1 1 _ _

noncomputable def qLeftFamily : M.toCollection.Family (M.profile (projection.map root)) :=
  projection.toHom.onFamily leftFamily
noncomputable def qRightFamily : M.toCollection.Family (M.profile (projection.map root)) :=
  projection.toHom.onFamily rightFamily

noncomputable def leftArrow : SemanticRefinement.Arrow M (projection.map root)
    (projection.map left) :=
  ⟨qLeftFamily, (projection.map_subst root leftFamily).symm.trans
    (congrArg projection.map graft_leftFamily)⟩
noncomputable def rightArrow : SemanticRefinement.Arrow M (projection.map root)
    (projection.map left) :=
  ⟨qRightFamily, (projection.map_subst root rightFamily).symm.trans
    ((congrArg projection.map graft_rightFamily).trans loop_groupings_equal_in_quotient.symm)⟩

theorem left_first_profile : M.profile (qLeftFamily (Sum.inl (Sum.inr ()))) = pairPath 1 1 1 := rfl
theorem right_first_profile : M.profile (qRightFamily (Sum.inl (Sum.inr ()))) = x.edge.toPath := rfl

theorem unequal_parallel_families : qLeftFamily ≠ qRightFamily := by
  intro h
  have he := congrFun h (Sum.inl (Sum.inr ()))
  have hp := congrArg (fun a : M.Op x => (M.profile a).length) he
  change 2 = 1 at hp
  cases hp

theorem unequal_parallel_arrows : leftArrow ≠ rightArrow := by
  intro h
  exact unequal_parallel_families (congrArg Subtype.val h)

theorem semantic_hom_not_subsingleton :
    ¬ Subsingleton (SemanticRefinement.Arrow M (projection.map root) (projection.map left)) := by
  intro h
  exact unequal_parallel_arrows (h.elim _ _)

/-- No lift of the right expansion to the fixed raw target L exists: changing
which original leaf is expanded changes the retained raw endpoint. -/
theorem right_expansion_has_no_fixed_target_lift :
    ¬ ∃ f : (collection S).Family (frontier root),
      profileGraft root f = left ∧ projection.toHom.onFamily f = qRightFamily := by
  rintro ⟨f, hf, he⟩
  have hσ : profileSubstitutionEquiv root f = profileSubstitutionEquiv root leftFamily := by
    apply Tree.graft_injective root
    rw [← profileGraft_eq_graft, ← profileGraft_eq_graft]
    exact hf.trans graft_leftFamily.symm
  have hfl : f = leftFamily := (profileSubstitutionEquiv root).injective hσ
  subst f
  exact unequal_parallel_families he

/-- Evaluation is compatible with an actual binary context. This is obtained
from the strict A3 projection law, never imposed as an equation on raw trees. -/
theorem map_join (a b c : Nat) (t : Tree S (component a b))
    (u : Tree S (component b c)) :
    projection.map (join a b c t u) =
      M.subst (projection.map (mu a b c))
        (projection.toHom.onFamily (Examples.binaryChildren t u)) :=
  (congrArg projection.map (graft_mu a b c t u)).symm.trans
    (projection.map_subst (mu a b c) (Examples.binaryChildren t u))

theorem map_join_congr (a b c : Nat)
    {t t' : Tree S (component a b)} {u u' : Tree S (component b c)}
    (ht : projection.map t = projection.map t')
    (hu : projection.map u = projection.map u') :
    projection.map (join a b c t u) = projection.map (join a b c t' u') := by
  rw [map_join, map_join]
  congr 1
  funext i
  rcases i with ((i | ⟨⟩) | ⟨⟩)
  · exact nomatch i
  · exact ht
  · exact hu

theorem map_context_congr {t u : Tree S x} (h : projection.map t = projection.map u) :
    projection.map (context t) = projection.map (context u) :=
  map_join_congr 0 1 2 rfl (map_join_congr 1 1 2 h rfl)

theorem mixed_groupings_equal_in_quotient : projection.map mixedLeft = projection.map mixedRight :=
  map_context_congr loop_groupings_equal_in_quotient

/-- Lift a forest through a fixed mixed-interface context without touching
its surrounding 0→1 and 1→2 leaves. -/
def contextSigma (σ : Substitution root) : Substitution mixedSource := by
  intro i
  rcases i with ((i | ⟨⟩) | ⟨⟩)
  · exact nomatch i
  · exact .leaf (component 0 1)
  · intro j
    rcases j with ((j | ⟨⟩) | ⟨⟩)
    · exact nomatch j
    · exact σ
    · exact .leaf (component 1 2)

theorem graft_contextSigma (σ : Substitution root) :
    graft mixedSource (contextSigma σ) = context (graft root σ) := by
  change Tree.node _ _ = Tree.node _ _
  congr 1
  funext i
  rcases i with ((i | ⟨⟩) | ⟨⟩)
  · exact nomatch i
  · rfl
  · change Tree.node _ _ = Tree.node _ _
    congr 1
    funext j
    rcases j with ((j | ⟨⟩) | ⟨⟩)
    · exact nomatch j
    · rfl
    · rfl

/-- The mixed certificate has independently refinable original loop slots 1 and 2.
The profile family is the exact A1 image of the displayed structural forest. -/
def mixedLeftFamily : (collection S).Family (frontier mixedSource) :=
  (profileSubstitutionEquiv mixedSource).symm
    (contextSigma (Examples.binaryChildren root (.leaf x)))
def mixedRightFamily : (collection S).Family (frontier mixedSource) :=
  (profileSubstitutionEquiv mixedSource).symm
    (contextSigma (Examples.binaryChildren (.leaf x) root))

theorem graft_mixedLeftFamily : profileGraft mixedSource mixedLeftFamily = mixedLeft := by
  rw [profileGraft_eq_graft]
  unfold mixedLeftFamily
  rw [Equiv.apply_symm_apply, graft_contextSigma]
  congr 1

theorem graft_mixedRightFamily : profileGraft mixedSource mixedRightFamily = mixedRight := by
  rw [profileGraft_eq_graft]
  unfold mixedRightFamily
  rw [Equiv.apply_symm_apply, graft_contextSigma]
  congr 1

noncomputable def mixedLeftArrow : SemanticRefinement.Arrow M (projection.map mixedSource)
    (projection.map mixedLeft) :=
  ⟨projection.toHom.onFamily mixedLeftFamily, (projection.map_subst mixedSource mixedLeftFamily).symm.trans
    (congrArg projection.map graft_mixedLeftFamily)⟩
noncomputable def mixedRightArrow : SemanticRefinement.Arrow M (projection.map mixedSource)
    (projection.map mixedLeft) :=
  ⟨projection.toHom.onFamily mixedRightFamily,
    (projection.map_subst mixedSource mixedRightFamily).symm.trans
      ((congrArg projection.map graft_mixedRightFamily).trans mixed_groupings_equal_in_quotient.symm)⟩

theorem mixed_unequal_parallel_arrows : mixedLeftArrow ≠ mixedRightArrow := by
  intro h
  have he := congrFun (congrArg Subtype.val h) (Sum.inl (Sum.inl (Sum.inr ())))
  have hp := congrArg (fun a : M.Op x => (M.profile a).length) he
  change 2 = 1 at hp
  cases hp

theorem mixed_semantic_hom_not_subsingleton :
    ¬ Subsingleton (SemanticRefinement.Arrow M (projection.map mixedSource)
      (projection.map mixedLeft)) := by
  intro h
  exact mixed_unequal_parallel_arrows (h.elim _ _)


/-- The corresponding raw arrows have different targets and each fixed hom is thin. -/
def rawLeftArrow : Raw.Arrow root left :=
  ⟨profileSubstitutionEquiv root leftFamily,
    (profileGraft_eq_graft root leftFamily).symm.trans graft_leftFamily⟩
def rawRightArrow : Raw.Arrow root right :=
  ⟨profileSubstitutionEquiv root rightFamily,
    (profileGraft_eq_graft root rightFamily).symm.trans graft_rightFamily⟩
theorem raw_fixed_hom_thin : Subsingleton (Raw.Arrow root left) := inferInstance

theorem projection_not_injective :
    ¬ Function.Injective (fun t : Tree S x => projection.map t) := by
  intro h
  exact loop_groupings_distinct (h loop_groupings_equal_in_quotient)

theorem mixed_right_expansion_has_no_fixed_target_lift :
    ¬ ∃ f : (collection S).Family (frontier mixedSource),
      profileGraft mixedSource f = mixedLeft ∧
        projection.toHom.onFamily f = projection.toHom.onFamily mixedRightFamily := by
  rintro ⟨f,hf,he⟩
  have hσ : profileSubstitutionEquiv mixedSource f =
      profileSubstitutionEquiv mixedSource mixedLeftFamily := by
    apply Tree.graft_injective mixedSource
    rw [← profileGraft_eq_graft, ← profileGraft_eq_graft]
    exact hf.trans graft_mixedLeftFamily.symm
  have hfl := (profileSubstitutionEquiv mixedSource).injective hσ
  subst f
  exact mixed_unequal_parallel_arrows (Subtype.ext he)

theorem mixed_witnesses_retained :
    projection.map (context (red 1 1)) ≠ projection.map (context (blue 1 1)) := by
  intro h
  have hw := quotient_retains_red_count h
  change 1 = 0 at hw
  cases hw

/-- A nullary insertion deletes just its original leaf's contribution to the
frontier; it does not delete the existing binary vertex. -/
def nullaryFamily : (collection S).Family (frontier root) :=
  Examples.binaryChildren (zero 1) (.leaf x)
def nullaryTarget : Tree S x := join 1 1 1 (zero 1) (.leaf x)
theorem graft_nullaryFamily : profileGraft root nullaryFamily = nullaryTarget :=
  graft_mu 1 1 1 _ _
theorem nullary_frontier_length : (frontier nullaryTarget).length = 1 := rfl
noncomputable def nullaryArrow : SemanticRefinement.Arrow M (projection.map root)
    (projection.map nullaryTarget) :=
  ⟨projection.toHom.onFamily nullaryFamily, (projection.map_subst root nullaryFamily).symm.trans
    (congrArg projection.map graft_nullaryFamily)⟩

def binaryWeight : Gen → Nat
  | .binary _ _ _ => 1
  | _ => 0

theorem declarations_preserve_binary : ∀ c p (a b : Operation (S := S) c p),
    equations c p a b → weight binaryWeight a.val = weight binaryWeight b.val := by
  intro c p a b h
  cases h
  rfl

theorem nullary_graft_not_a_unit : projection.map nullaryTarget ≠ projection.map (.leaf x) := by
  intro h
  have hw := Presentation.derives_weight equations binaryWeight declarations_preserve_binary
    ((Presentation.quotient_eq_iff equations _ _).1 h)
  change 1 = 0 at hw
  cases hw

/-- An additional nonidentity refinement at the first of the three final leaves. -/
def addRedFamily : (collection S).Family (frontier left)
  | .inl (.inl (.inl i)) => nomatch i
  | .inl (.inl (.inr ())) => red 1 1
  | .inl (.inr ()) => .leaf x
  | .inr () => .leaf x

def redTarget : Tree S x := profileGraft left addRedFamily
noncomputable def addRedArrow : SemanticRefinement.Arrow M (projection.map left)
    (projection.map redTarget) :=
  ⟨projection.toHom.onFamily addRedFamily, (projection.map_subst left addRedFamily).symm⟩

theorem addRed_changes_object : projection.map redTarget ≠ projection.map left := by
  intro h
  have hw := quotient_retains_red_count h
  unfold redTarget at hw
  rw [weight_profileGraft] at hw
  change 1 = 0 at hw
  cases hw

noncomputable def leftThenRedArrow : SemanticRefinement.Arrow M (projection.map root)
    (projection.map redTarget) := SemanticRefinement.comp leftArrow addRedArrow
noncomputable def rightThenRedArrow : SemanticRefinement.Arrow M (projection.map root)
    (projection.map redTarget) := SemanticRefinement.comp rightArrow addRedArrow

theorem composed_left_endpoint : M.subst (projection.map root) leftThenRedArrow.val =
    projection.map redTarget := leftThenRedArrow.property
theorem composed_right_endpoint : M.subst (projection.map root) rightThenRedArrow.val =
    projection.map redTarget := rightThenRedArrow.property

end WitnessedDecompositions.RefinementExamples


