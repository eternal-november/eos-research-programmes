module

public import WitnessedDecompositions.FreeExtension

/-!
C2 local optional Lean slice. Generic relation-interface calculi over an arbitrary
family of carrier types, hence in particular all finite families including empty
carriers. Containment and equality are separate operation conditions. The full
C2 obligation remains OPEN pending future D2/E integration.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
universe u v w z
namespace WitnessedDecompositions.RelationInterface

/-- A wrapper keeps this relation quiver distinct from any other instance on I. -/
structure Interface (I : Type u) (X : I → Type v) where
  label : I

variable {I : Type u} {X : I → Type v}

instance relationQuiver : Quiver.{v} (Interface I X) where
  Hom a b := X a.label → X b.label → Prop

abbrev Rel (a b : Interface I X) := a ⟶ b
abbrev Included {a b : Interface I X} (R S : Rel a b) := ∀ x y, R x y → S x y

def diagonal (a : Interface I X) : Rel a a := fun x y => x = y

def comp {a b c : Interface I X} (R : Rel a b) (S : Rel b c) : Rel a c :=
  fun x z => ∃ y, R x y ∧ S y z

@[simp] theorem comp_diagonal_left {a b : Interface I X} (R : Rel a b) :
    comp (diagonal a) R = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, rfl, h⟩
    exact h
  · intro h
    exact ⟨x, rfl, h⟩

@[simp] theorem comp_diagonal_right {a b : Interface I X} (R : Rel a b) :
    comp R (diagonal b) = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, h, rfl⟩
    exact h
  · intro h
    exact ⟨y, h, rfl⟩

theorem comp_assoc {a b c d : Interface I X}
    (R : Rel a b) (S : Rel b c) (T : Rel c d) :
    comp (comp R S) T = comp R (comp S T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, hr, hs⟩, ht⟩
    exact ⟨y, hr, z, hs, ht⟩
  · rintro ⟨y, hr, z, hs, ht⟩
    exact ⟨z, ⟨y, hr, hs⟩, ht⟩

theorem comp_mono {a b c : Interface I X} {R R' : Rel a b} {S S' : Rel b c}
    (hR : Included R R') (hS : Included S S') :
    Included (comp R S) (comp R' S') := by
  rintro x z ⟨y, hr, hs⟩
  exact ⟨y, hR x y hr, hS y z hs⟩

/-- Full existential path composite; the zero-arity value is the diagonal. -/
def evaluate {a : Interface I X} : {b : Interface I X} → Quiver.Path a b → Rel a b
  | _, .nil => diagonal a
  | _, .cons p r => comp (evaluate p) r

@[simp] theorem evaluate_nil (a : Interface I X) :
    evaluate (Quiver.Path.nil : Quiver.Path a a) = diagonal a := rfl

@[simp] theorem evaluate_edge {a b : Interface I X} (R : Rel a b) :
    evaluate R.toPath = R := comp_diagonal_left R

theorem evaluate_comp {a b c : Interface I X}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    evaluate (p.comp q) = comp (evaluate p) (evaluate q) := by
  induction q with
  | nil => exact (comp_diagonal_right _).symm
  | cons q r ih =>
    change comp (evaluate (p.comp q)) r = comp (evaluate p) (comp (evaluate q) r)
    rw [ih, comp_assoc]

/-- Substitution existence: independently replace each occurrence by any
path whose composite is contained in that occurrence's component. -/
theorem evaluate_expand_le {a b : Interface I X} (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (h : ∀ i, Included (evaluate (q i)) (Path.componentAt p i).edge) :
    Included (evaluate (Path.expand p q)) (evaluate p) := by
  induction p with
  | nil => exact fun _ _ h => h
  | cons p r ih =>
    change Included (evaluate ((Path.expand p (fun i => q (.inl i))).comp (q (.inr ()))))
      (comp (evaluate p) r)
    rw [evaluate_comp]
    exact comp_mono (ih (fun i => q (.inl i)) (fun i => h (.inl i))) (h (.inr ()))

/-- Exact substitution is a separate stronger condition. -/
theorem evaluate_expand_eq {a b : Interface I X} (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (h : ∀ i, evaluate (q i) = (Path.componentAt p i).edge) :
    evaluate (Path.expand p q) = evaluate p := by
  induction p with
  | nil => rfl
  | cons p r ih =>
    change evaluate ((Path.expand p (fun i => q (.inl i))).comp (q (.inr ()))) =
      comp (evaluate p) r
    rw [evaluate_comp, ih (fun i => q (.inl i)) (fun i => h (.inl i)), h (.inr ())]
    rfl

/-- Total operations retain their entire path and output component.
Only the containment proof is proof-irrelevant. -/
def ContainmentOp (c : Component (Interface I X)) :=
  {p : Quiver.Path c.source c.target // Included (evaluate p) c.edge}

def ExactOp (c : Component (Interface I X)) :=
  {p : Quiver.Path c.source c.target // evaluate p = c.edge}

def containmentData : CalcData (Interface I X) where
  Op := ContainmentOp
  profile a := a.val
  identity c := ⟨c.edge.toPath, by rw [evaluate_edge]; exact fun _ _ h => h⟩
  profile_identity _ := rfl
  subst a f := ⟨Path.expand a.val (fun i => (f i).val), by
    intro x y h
    exact a.property x y (evaluate_expand_le a.val (fun i => (f i).val)
      (fun i => (f i).property) x y h)⟩
  profile_subst _ _ := rfl

def exactData : CalcData (Interface I X) where
  Op := ExactOp
  profile a := a.val
  identity c := ⟨c.edge.toPath, evaluate_edge c.edge⟩
  profile_identity _ := rfl
  subst a f := ⟨Path.expand a.val (fun i => (f i).val),
    (evaluate_expand_eq a.val (fun i => (f i).val) (fun i => (f i).property)).trans a.property⟩
  profile_subst _ _ := rfl

/-- The actual public A `Calc`, not just a private look-alike record. -/
def containmentCalc : Calc (Interface I X) where
  toCalcData := containmentData
  subst_identity a := by
    apply Subtype.ext
    exact Path.expand_edges a.val
  identity_subst a := by
    apply Subtype.ext
    exact Quiver.Path.nil_comp a.val
  subst_assoc a f h := by
    apply Subtype.ext
    exact (containmentData.composeAt_profile f h)

/-- The exact subcalculus uses equality, never containment as an alias. -/
def exactCalc : Calc (Interface I X) where
  toCalcData := exactData
  subst_identity a := by
    apply Subtype.ext
    exact Path.expand_edges a.val
  identity_subst a := by
    apply Subtype.ext
    exact Quiver.Path.nil_comp a.val
  subst_assoc a f h := by
    apply Subtype.ext
    exact (exactData.composeAt_profile f h)

/-- Strict means preserving structure literally; properness is not asserted
for degenerate empty families. -/
def exactInclusion : Calc.Hom (exactCalc (X := X)) containmentCalc where
  map a := ⟨a.val, by rw [a.property]; exact fun _ _ h => h⟩
  profile_map _ := rfl
  map_identity _ := rfl
  map_subst _ _ := rfl

/-- Explicit two-sided bridge from the public prescribed-profile fibre to
the singleton-or-empty containment convention. -/
def containmentFiberEquiv (c : Component (Interface I X))
    (p : Quiver.Path c.source c.target) :
    (containmentCalc (X := X)).Operation c p ≃
      { _u : Unit // Included (evaluate p) c.edge } where
  toFun a := ⟨(), by rw [← a.property]; exact a.val.property⟩
  invFun h := ⟨⟨p, h.property⟩, rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact a.property.symm
  right_inv a := by
    apply Subtype.ext
    exact Subsingleton.elim _ _

/-- Equality fibres are compared separately, not defined using containment. -/
def exactFiberEquiv (c : Component (Interface I X))
    (p : Quiver.Path c.source c.target) :
    (exactCalc (X := X)).Operation c p ≃
      { _u : Unit // evaluate p = c.edge } where
  toFun a := ⟨(), by rw [← a.property]; exact a.val.property⟩
  invFun h := ⟨⟨p, h.property⟩, rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact a.property.symm
  right_inv a := by
    apply Subtype.ext
    exact Subsingleton.elim _ _

/-- Posetal means a fixed full profile/output fibre has at most one cell; it
never means all total operations or all syntax trees are equal. -/
theorem containment_fiber_subsingleton (c : Component (Interface I X))
    (p : Quiver.Path c.source c.target) :
    Subsingleton ((containmentCalc (X := X)).Operation c p) := by
  constructor
  intro a b
  apply Subtype.ext
  apply Subtype.ext
  exact a.property.trans b.property.symm

theorem exact_fiber_subsingleton (c : Component (Interface I X))
    (p : Quiver.Path c.source c.target) :
    Subsingleton ((exactCalc (X := X)).Operation c p) := by
  constructor
  intro a b
  apply Subtype.ext
  apply Subtype.ext
  exact a.property.trans b.property.symm

section PublicExtension
variable (S : Signature (Interface I X))

/-- A primitive label is interpreted only after its full typed profile/whole
containment is supplied. Distinct labels remain distinct in the source. -/
def primitiveAssignment
    (valid : ∀ g, Included (evaluate (S.input g)) (S.output g)) :
    S.Assignment containmentCalc :=
  fun g => ⟨⟨S.input g, valid g⟩, rfl⟩

/-- Instantiation of the genuine A2 extension into the actual relational Calc. -/
def presentationExtension
    (valid : ∀ g, Included (evaluate (S.input g)) (S.output g)) :
    Calc.Hom (Tree.freeCalc S) containmentCalc :=
  Tree.extend containmentCalc (primitiveAssignment S valid)

theorem presentationExtension_unique
    (valid : ∀ g, Included (evaluate (S.input g)) (S.output g))
    (F : Calc.Hom (Tree.freeCalc S) containmentCalc)
    (h : Tree.restrict containmentCalc F = primitiveAssignment S valid) :
    F = presentationExtension S valid :=
  Tree.extend_unique containmentCalc (primitiveAssignment S valid) F h

/-- Semantic loss: parallel presentations have equal relational values. This
statement deliberately has no conclusion asserting equality of trees. -/
theorem same_frontier_same_semantics
    (valid : ∀ g, Included (evaluate (S.input g)) (S.output g))
    {c : Component (Interface I X)} (t t' : Tree S c)
    (h : t.frontier = t'.frontier) :
    (presentationExtension S valid).map t = (presentationExtension S valid).map t' := by
  apply Subtype.ext
  exact ((presentationExtension S valid).profile_map t).trans
    (h.trans ((presentationExtension S valid).profile_map t').symm)

end PublicExtension

section Restriction
variable {Y : I → Type w} {Z : I → Type z}

/-- Contravariant restriction on components, assembled as a quiver map.
The source and target quivers generally differ, so this is NOT `Calc.Hom`. -/
def restrictionQuiver (f : ∀ i, Y i → X i) : Interface I X ⥤q Interface I Y where
  obj a := ⟨a.label⟩
  map {a b} R := fun x y => R (f a.label x) (f b.label y)

def restrictionComponent (f : ∀ i, Y i → X i) (c : Component (Interface I X)) :
    Component (Interface I Y) :=
  ⟨(restrictionQuiver f).obj c.source, (restrictionQuiver f).obj c.target,
    (restrictionQuiver f).map c.edge⟩

/-- The comparison maps actual existential witnesses through the boundary maps.
All arities, including zero, are covered without an inhabitance assumption. -/
theorem restriction_path_comparison (f : ∀ i, Y i → X i)
    {a b : Interface I X} (p : Quiver.Path a b) :
    Included (evaluate ((restrictionQuiver f).mapPath p))
      ((restrictionQuiver f).map (evaluate p)) := by
  induction p with
  | nil =>
    intro x y h
    exact congrArg (f _) h
  | @cons b c p R ih =>
    rintro x z ⟨y, hp, hr⟩
    exact ⟨f b.label y, ih x y hp, hr⟩

/-- A total containment cell always restricts, retaining its independently
supplied whole as its pulled-back output component. -/
def restrictContainment (f : ∀ i, Y i → X i) {c : Component (Interface I X)}
    (a : ContainmentOp c) : ContainmentOp (restrictionComponent f c) :=
  ⟨(restrictionQuiver f).mapPath a.val, fun x y h =>
    a.property (f _ x) (f _ y) (restriction_path_comparison f a.val x y h)⟩

@[simp] theorem restriction_identity :
    restrictionQuiver (fun i (x : X i) => x) = 𝟭q (Interface I X) := rfl

@[simp] theorem restriction_composite (f : ∀ i, Y i → X i) (g : ∀ i, Z i → Y i) :
    restrictionQuiver (fun i x => f i (g i x)) =
      (restrictionQuiver f) ⋙q (restrictionQuiver g) := rfl

@[simp] theorem restriction_path_identity {a b : Interface I X} (p : Quiver.Path a b) :
    (restrictionQuiver (fun i (x : X i) => x)).mapPath p = p := by
  exact Prefunctor.mapPath_id p

theorem restriction_path_composite (f : ∀ i, Y i → X i) (g : ∀ i, Z i → Y i)
    {a b : Interface I X} (p : Quiver.Path a b) :
    (restrictionQuiver (fun i x => f i (g i x))).mapPath p =
      (restrictionQuiver g).mapPath ((restrictionQuiver f).mapPath p) := by
  exact Prefunctor.mapPath_comp_apply (restrictionQuiver f) (restrictionQuiver g) p

/-- Binary equality when the middle boundary map is onto. Endpoints need not
be onto or one-to-one. This is sufficient, not the full deferred D2 criterion. -/
theorem restriction_binary_eq_of_surjective (f : ∀ i, Y i → X i)
    {a b c : Interface I X} (R : Rel a b) (S : Rel b c)
    (onto : Function.Surjective (f b.label)) :
    comp ((restrictionQuiver f).map R) ((restrictionQuiver f).map S) =
      (restrictionQuiver f).map (comp R S) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hr, hs⟩
    exact ⟨f b.label y, hr, hs⟩
  · rintro ⟨y, hr, hs⟩
    obtain ⟨y', rfl⟩ := onto y
    exact ⟨y', hr, hs⟩

/-- Every positive-arity path has equality when each internal boundary map is
onto. Only targets of the prefix edges are requested; neither endpoint is. -/
theorem restriction_nonempty_eq_of_surjective (f : ∀ i, Y i → X i)
    {a b c : Interface I X} (p : Quiver.Path a b) (R : Rel b c)
    (onto : ∀ i : Path.Slot p,
      Function.Surjective (f (Path.componentAt p i).target.label)) :
    evaluate ((restrictionQuiver f).mapPath (p.cons R)) =
      (restrictionQuiver f).map (evaluate (p.cons R)) := by
  induction p generalizing c with
  | nil =>
    change evaluate ((restrictionQuiver f).map R).toPath =
      (restrictionQuiver f).map (evaluate R.toPath)
    rw [evaluate_edge, evaluate_edge]
  | @cons b d p S ih =>
    change comp (evaluate ((restrictionQuiver f).mapPath (p.cons S)))
      ((restrictionQuiver f).map R) =
      (restrictionQuiver f).map (comp (evaluate (p.cons S)) R)
    rw [ih S (fun i => onto (.inl i))]
    exact restriction_binary_eq_of_surjective f (evaluate (p.cons S)) R (onto (.inr ()))

/-- The pullback of a diagonal is a kernel pair, NOT generally a diagonal. -/
theorem restriction_nullary_kernel (f : ∀ i, Y i → X i)
    (a : Interface I X) (x y : Y a.label) :
    (restrictionQuiver f).map (evaluate (Quiver.Path.nil : Quiver.Path a a)) x y ↔
      f a.label x = f a.label y := Iff.rfl

/-- Exact restriction of the zero-input diagonal is precisely injectivity. -/
theorem restriction_nullary_eq_iff (f : ∀ i, Y i → X i) (a : Interface I X) :
    evaluate ((restrictionQuiver f).mapPath (Quiver.Path.nil : Quiver.Path a a)) =
      (restrictionQuiver f).map (evaluate (Quiver.Path.nil : Quiver.Path a a)) ↔
      Function.Injective (f a.label) := by
  constructor
  · intro h x y hxy
    have hh := congrFun (congrFun h x) y
    exact hh.mpr hxy
  · intro h
    funext x y
    apply propext
    exact ⟨fun hxy => congrArg (f a.label) hxy, fun hxy => h hxy⟩

end Restriction

/-- A nonexact witness is permitted whenever an output relation strictly
contains the path composite; the whole is not defined to be that composite. -/
theorem diagonal_containment_nonexact (a : Interface I X)
    (x y : X a.label) (hne : x ≠ y) :
    Included (evaluate ((diagonal a).toPath)) (fun _ _ => True) ∧
    evaluate ((diagonal a).toPath) ≠ (fun _ _ => True) := by
  rw [evaluate_edge]
  refine ⟨fun _ _ _ => True.intro, ?_⟩
  intro h
  have hh := congrFun (congrFun h x) y
  exact hne (hh.mpr True.intro)

end WitnessedDecompositions.RelationInterface
