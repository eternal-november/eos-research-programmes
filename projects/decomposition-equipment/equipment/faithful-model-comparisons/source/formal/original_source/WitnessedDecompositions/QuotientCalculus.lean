module

public import WitnessedDecompositions.Congruence

/-! Generic quotients by arbitrary parallel substitution congruences.
Representative selection uses standard classical choice through Quotient.out;
no normal form, convergence, or decidability is assumed. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v z z' z'' z'''

namespace WitnessedDecompositions
namespace ParallelCongruence
variable {V : Type u} [Quiver.{v} V] {M : Calc.{u, v, z} V}

/-- The quotient retains the full ordered profile, which descends by parallelism. -/
def quotientCollection (R : ParallelCongruence M) : Collection.{u, v, z} V where
  Op c := Quotient (R.setoid c)
  profile := Quotient.lift M.profile (fun _ _ h => R.parallel h)

/-- The quotient map before imposing the calculus laws. -/
def projectCollection (R : ParallelCongruence M) :
    Collection.Hom M.toCollection R.quotientCollection where
  map := Quotient.mk _
  profile_map _ := rfl

@[simp] theorem project_out (R : ParallelCongruence M) {c : Component V}
    (a : R.quotientCollection.Op c) : R.projectCollection.map (Quotient.out a) = a :=
  Quotient.out_eq a

@[simp] theorem profile_out (R : ParallelCongruence M) {c : Component V}
    (a : R.quotientCollection.Op c) : M.profile (Quotient.out a) =
      R.quotientCollection.profile a := by
  exact congrArg R.quotientCollection.profile (R.project_out a)

/-- Every quotient operation in a prescribed fibre has a representative in that
same fibre, not merely a representative with the same arity or endpoints. -/
noncomputable def representativeOperation (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (a : R.quotientCollection.Fiber c p) : M.Operation c p :=
  ⟨Quotient.out a.val, (R.profile_out a.val).trans a.property⟩

def projectOperation (R : ParallelCongruence M) {c : Component V}
    {p : Quiver.Path c.source c.target} (a : M.Operation c p) :
    R.quotientCollection.Fiber c p := R.projectCollection.onFiber a

@[simp] theorem project_representative (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (a : R.quotientCollection.Fiber c p) :
    R.projectOperation (R.representativeOperation a) = a := by
  apply Subtype.ext
  exact R.project_out a.val

/-- Arbitrary independently prescribed replacement fibres, including empty
families and repeated colours, admit simultaneous lifts. -/
theorem projectOperation_surjective (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target} :
    Function.Surjective (fun a : M.Operation c p => R.projectOperation a) :=
  fun a => ⟨R.representativeOperation a, R.project_representative a⟩

/-- Actual quotient substitution in every prescribed operation fibre. -/
noncomputable def quotientSubstitute (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (a : R.quotientCollection.Fiber c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, R.quotientCollection.Fiber (Path.componentAt p i) (q i)) :
    R.quotientCollection.Fiber c (Path.expand p q) :=
  R.projectOperation (M.substitute (R.representativeOperation a) q
    (fun i => R.representativeOperation (f i)))

/-- Representative independence, simultaneously for outer operations and every
independently chosen operation in its prescribed input fibre. -/
theorem quotientSubstitute_project (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target} (a : M.Operation c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i)) :
    R.quotientSubstitute (R.projectOperation a) q (fun i => R.projectOperation (f i)) =
      R.projectOperation (M.substitute a q f) := by
  apply Subtype.ext
  apply Quotient.sound
  apply R.substitute
  · exact Quotient.exact (R.project_out (R.projectCollection.map a.val))
  · intro i
    exact Quotient.exact (R.project_out (R.projectCollection.map (f i).val))

/-- Quotient data use the actual prescribed-fibre substitution above. -/
noncomputable def quotientData (R : ParallelCongruence M) : CalcData.{u, v, z} V where
  toCollection := R.quotientCollection
  identity c := R.projectCollection.map (M.identity c)
  profile_identity := M.profile_identity
  subst a f := (R.quotientSubstitute ⟨a, rfl⟩
    (fun i => R.quotientCollection.profile (f i)) (fun i => ⟨f i, rfl⟩)).val
  profile_subst a f := (R.quotientSubstitute ⟨a, rfl⟩
    (fun i => R.quotientCollection.profile (f i)) (fun i => ⟨f i, rfl⟩)).property

/-- Strict preservation of total simultaneous substitution by the quotient map. -/
theorem project_subst (R : ParallelCongruence M) {c : Component V}
    (a : M.Op c) (f : M.toCollection.Family (M.profile a)) :
    R.projectCollection.map (M.subst a f) =
      R.quotientData.subst (R.projectCollection.map a) (R.projectCollection.onFamily f) := by
  exact (congrArg Subtype.val (R.quotientSubstitute_project
    (⟨a, rfl⟩ : M.Operation c (M.profile a))
    (fun i => M.profile (f i)) (fun i => ⟨f i, rfl⟩))).symm

/-- Every total replacement family lifts pointwise. No finite choice principle
or inhabited-operation-space assumption is imposed. -/
theorem projectFamily_surjective (R : ParallelCongruence M) {a b : V}
    (p : Quiver.Path a b) : Function.Surjective
      (fun f : M.toCollection.Family p => R.projectCollection.onFamily f) := by
  intro f
  refine ⟨(fun i => Quotient.out (f i)), ?_⟩
  funext i
  exact R.project_out (f i)


/-- Quotient substitution has the right unit at every output component. -/
theorem quotient_subst_identity (R : ParallelCongruence M) {c : Component V}
    (a : R.quotientCollection.Op c) :
    R.quotientData.subst a (R.quotientData.identityFamily (R.quotientData.profile a)) = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
    change R.quotientData.subst (R.projectCollection.map a)
      (R.projectCollection.onFamily (M.toCalcData.identityFamily (M.profile a))) = _
    rw [← R.project_subst, M.subst_identity]
    rfl

/-- Quotient substitution has the left unit, also for nullary inserted operations. -/
theorem quotient_identity_subst (R : ParallelCongruence M) {c : Component V}
    (a : R.quotientCollection.Op c) :
    R.quotientData.subst (R.quotientData.identity c)
      (R.quotientCollection.reindex (R.quotientData.profile_identity c)
        (R.quotientCollection.singletonFamily a)) = a := by
  induction a using Quotient.inductionOn with
  | _ a =>
    have he : R.quotientCollection.singletonFamily (R.projectCollection.map a) =
      R.projectCollection.onFamily (M.toCollection.singletonFamily a) := by
      funext i
      rcases i with i | ⟨⟩
      · exact nomatch i
      · rfl
    change R.quotientData.subst (R.projectCollection.map (M.identity c))
      (R.quotientCollection.reindex (M.profile_identity c)
        (R.quotientCollection.singletonFamily (R.projectCollection.map a))) = _
    rw [he, ← Collection.Hom.onFamily_reindex, ← R.project_subst, M.identity_subst]
    rfl


/-- A typed substitution depends on its operation, not the proof of its profile. -/
theorem quotient_subst_congr (R : ParallelCongruence M) {c : Component V}
    {a b : R.quotientCollection.Op c} (hab : a = b)
    {p : Quiver.Path c.source c.target}
    (ha : R.quotientCollection.profile a = p) (hb : R.quotientCollection.profile b = p)
    (f : R.quotientCollection.Family p) :
    R.quotientData.subst a (R.quotientCollection.reindex ha f) =
      R.quotientData.subst b (R.quotientCollection.reindex hb f) := by
  cases hab
  rfl

/-- Component equality transport commutes with projection. -/
theorem project_occurrenceTransport (R : ParallelCongruence M)
    {c d : Component V} (h : c = d) (a : M.Op c) :
    R.projectCollection.map (Path.occurrenceTransport M.Op h a) =
      Path.occurrenceTransport R.quotientCollection.Op h (R.projectCollection.map a) := by
  cases h
  rfl

/-- Projection commutes with restricting a family to an inserted occurrence. -/
theorem project_expandFamily (R : ParallelCongruence M) {a b : V}
    (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (h : M.toCollection.Family (Path.expand p q)) (i : Path.Slot p) :
    R.projectCollection.onFamily (Path.expandFamily M.Op p q h i) =
      Path.expandFamily R.quotientCollection.Op p q (R.projectCollection.onFamily h) i := by
  funext j
  exact R.project_occurrenceTransport _ _

/-- Canonical two-layer family composition is preserved, including every occurrence transport. -/
theorem project_composeAt (R : ParallelCongruence M) {a b : V}
    {p : Quiver.Path a b} (f : M.toCollection.Family p)
    (h : M.toCollection.Family (M.toCollection.familyProfile f)) :
    R.projectCollection.onFamily (M.toCalcData.composeAt f h) =
      R.quotientData.composeAt (R.projectCollection.onFamily f) (R.projectCollection.onFamily h) := by
  funext i
  change R.projectCollection.map (M.subst (f i) _) = R.quotientData.subst (R.projectCollection.map (f i)) _
  rw [R.project_subst]
  congr 1
  exact R.project_expandFamily p (fun i => M.profile (f i)) h i

/-- Associativity on arbitrary expanded-profile replacement families. -/
theorem quotient_subst_assocAt (R : ParallelCongruence M) {c : Component V}
    (a : R.quotientCollection.Op c)
    (f : R.quotientCollection.Family (R.quotientCollection.profile a))
    (h : R.quotientCollection.Family (R.quotientCollection.familyProfile f)) :
    R.quotientData.subst (R.quotientData.subst a f)
      (R.quotientCollection.reindex (R.quotientData.profile_subst a f) h) =
      R.quotientData.subst a (R.quotientData.composeAt f h) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    rcases R.projectFamily_surjective (M.profile a) f with ⟨fs, rfl⟩
    rcases R.projectFamily_surjective (M.toCollection.familyProfile fs) h with ⟨hs, rfl⟩
    change R.quotientData.subst
      (R.quotientData.subst (R.projectCollection.map a) (R.projectCollection.onFamily fs))
      (R.quotientCollection.reindex _ (R.projectCollection.onFamily hs)) =
      R.quotientData.subst (R.projectCollection.map a)
        (R.quotientData.composeAt (R.projectCollection.onFamily fs) (R.projectCollection.onFamily hs))
    rw [R.quotient_subst_congr (R.project_subst a fs).symm _ (M.profile_subst a fs)]
    rw [← Collection.Hom.onFamily_reindex, ← R.project_subst]
    have hassoc := congrArg Subtype.val (M.substituteFamily_assoc
      (⟨a, rfl⟩ : M.Operation c (M.profile a)) fs hs)
    change M.subst (M.subst a fs) (M.toCollection.reindex (M.profile_subst a fs) hs) =
      M.subst a (M.toCalcData.composeAt fs hs) at hassoc
    rw [hassoc, R.project_subst, R.project_composeAt]

/-- The actual total-space associativity law uses CalcData.composeFamily,
with no substitute associator or tree-specific assumption. -/
theorem quotient_subst_assoc (R : ParallelCongruence M) {c : Component V}
    (a : R.quotientCollection.Op c)
    (f : R.quotientCollection.Family (R.quotientCollection.profile a))
    (h : R.quotientCollection.Family (R.quotientData.profile (R.quotientData.subst a f))) :
    R.quotientData.subst (R.quotientData.subst a f) h =
      R.quotientData.subst a (R.quotientData.composeFamily a f h) := by
  have hh := R.quotient_subst_assocAt a f
    (R.quotientCollection.reindex (R.quotientData.profile_subst a f).symm h)
  rw [Collection.reindex_comp] at hh
  exact hh


/-- The genuine quotient calculus of an arbitrary parallel substitution congruence. -/
noncomputable def quotient (R : ParallelCongruence M) : Calc.{u, v, z} V where
  toCalcData := R.quotientData
  subst_identity := R.quotient_subst_identity
  identity_subst := R.quotient_identity_subst
  subst_assoc := R.quotient_subst_assoc

/-- The strict quotient projection preserves the complete ordered profile. -/
noncomputable def projection (R : ParallelCongruence M) : Calc.Hom M R.quotient where
  toHom := R.projectCollection
  map_identity _ := rfl
  map_subst := R.project_subst

/-- Quotient equality is exactly the declared congruence, not equality in a chosen model. -/
theorem quotient_eq_iff (R : ParallelCongruence M) {c : Component V} (a b : M.Op c) :
    R.projection.map a = R.projection.map b ↔ R.Rel a b :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- The quotient is onto in every prescribed ordered-profile fibre. -/
theorem projection_onOperation_surjective (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target} :
    Function.Surjective (fun a : M.Operation c p => R.projection.onOperation a) :=
  R.projectOperation_surjective

/-- The named prescribed-fibre construction is the quotient calculus's actual
substitution, rather than an auxiliary operation with unproved agreement. -/
theorem quotient_substitute_eq (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (a : R.quotient.Operation c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, R.quotient.Operation (Path.componentAt p i) (q i)) :
    R.quotient.substitute a q f = R.quotientSubstitute a q f := by
  rcases R.projection_onOperation_surjective a with ⟨a, rfl⟩
  let fs := fun i => R.representativeOperation (f i)
  have hf : (fun i => R.projection.onOperation (fs i)) = f := by
    funext i
    exact R.project_representative (f i)
  rw [← hf, ← R.projection.onOperation_substitute]
  exact (R.quotientSubstitute_project a q fs).symm

/-- A strict map respects a congruence when it identifies every related pair. -/
def Respects (R : ParallelCongruence M) {N : Calc.{u, v, z'} V} (F : Calc.Hom M N) : Prop :=
  ∀ {c : Component V} {a b : M.Op c}, R.Rel a b → F.map a = F.map b

/-- A quotient-respecting strict map descends to the quotient as a strict map. -/
noncomputable def factor (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (F : Calc.Hom M N) (hF : R.Respects F) : Calc.Hom R.quotient N where
  map := Quotient.lift F.map (fun _ _ h => hF h)
  profile_map a := by
    induction a using Quotient.inductionOn with
    | _ a => exact F.profile_map a
  map_identity := F.map_identity
  map_subst a f := by
    induction a using Quotient.inductionOn with
    | _ a =>
      rcases R.projectFamily_surjective (M.profile a) f with ⟨fs, rfl⟩
      change Quotient.lift F.map (fun _ _ h => hF h)
        (R.quotientData.subst (R.projectCollection.map a) (R.projectCollection.onFamily fs)) = _
      rw [← R.project_subst]
      exact F.map_subst a fs

@[simp] theorem factor_map_projection (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (F : Calc.Hom M N) (hF : R.Respects F) {c : Component V} (a : M.Op c) :
    (R.factor F hF).map (R.projection.map a) = F.map a := rfl

/-- The descended strict map factors the original strict map exactly. -/
@[simp] theorem projection_factor (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (F : Calc.Hom M N) (hF : R.Respects F) :
    R.projection.comp (R.factor F hF) = F := by
  apply Calc.Hom.ext
  intros
  rfl

/-- No other strict quotient map can have the same composite with projection. -/
theorem factor_unique (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (F : Calc.Hom M N) (hF : R.Respects F) (G : Calc.Hom R.quotient N)
    (hG : R.projection.comp G = F) : G = R.factor F hF := by
  apply Calc.Hom.ext
  intro c a
  induction a using Quotient.inductionOn with
  | _ a => exact congrArg (fun H : Calc.Hom M N => H.map a) hG

/-- Projection itself respects the congruence. -/
theorem projection_respects (R : ParallelCongruence M) : R.Respects R.projection :=
  fun h => Quotient.sound h

/-- Factoring the projection yields the identity strict quotient morphism. -/
@[simp] theorem factor_projection (R : ParallelCongruence M) :
    R.factor R.projection R.projection_respects = Calc.Hom.id R.quotient := by
  symm
  apply R.factor_unique
  exact Calc.Hom.comp_id _

/-- Respect for the congruence is preserved by arbitrary strict postcomposition. -/
theorem respects_comp (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    {P : Calc.{u, v, z''} V} (F : Calc.Hom M N) (hF : R.Respects F)
    (G : Calc.Hom N P) : R.Respects (F.comp G) :=
  fun h => congrArg G.map (hF h)

/-- The factorization is natural in the target calculus. -/
theorem factor_comp (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    {P : Calc.{u, v, z''} V} (F : Calc.Hom M N) (hF : R.Respects F)
    (G : Calc.Hom N P) :
    R.factor (F.comp G) (R.respects_comp F hF G) = (R.factor F hF).comp G := by
  symm
  apply R.factor_unique
  rw [← Calc.Hom.comp_assoc, R.projection_factor]


/-- Simultaneously replacing every representative by a congruent one changes
neither the actual quotient operation nor its prescribed expanded profile. -/
theorem projection_substitute_eq_of_rel (R : ParallelCongruence M)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (a b : M.Operation c p) (hab : R.Rel a.val b.val)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f g : ∀ i : Path.Slot p, M.Operation (Path.componentAt p i) (q i))
    (hfg : ∀ i, R.Rel (f i).val (g i).val) :
    R.projection.onOperation (M.substitute a q f) =
      R.projection.onOperation (M.substitute b q g) := by
  apply Subtype.ext
  exact Quotient.sound (R.substitute a b hab q f g hfg)

/-- Precomposition with projection always produces a congruence-respecting map. -/
theorem projection_comp_respects (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (G : Calc.Hom R.quotient N) : R.Respects (R.projection.comp G) :=
  R.respects_comp R.projection R.projection_respects G

/-- The unrestricted strict-map universal property, as an explicit hom-set bijection. -/
noncomputable def homEquiv (R : ParallelCongruence M) (N : Calc.{u, v, z'} V) :
    Calc.Hom R.quotient N ≃ {F : Calc.Hom M N // R.Respects F} where
  toFun G := ⟨R.projection.comp G, R.projection_comp_respects G⟩
  invFun F := R.factor F.val F.property
  left_inv G := (R.factor_unique _ _ G rfl).symm
  right_inv F := Subtype.ext (R.projection_factor F.val F.property)

/-- Compatibility of a strict map with chosen source and target congruences. -/
def MapsTo (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (T : ParallelCongruence N) (F : Calc.Hom M N) : Prop :=
  ∀ {c : Component V} {a b : M.Op c}, R.Rel a b → T.Rel (F.map a) (F.map b)

/-- A compatible strict map induces a strict map between quotient calculi. -/
noncomputable def quotientMap (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (T : ParallelCongruence N) (F : Calc.Hom M N) (hF : R.MapsTo T F) :
    Calc.Hom R.quotient T.quotient :=
  R.factor (F.comp T.projection) (fun h => Quotient.sound (hF h))

/-- Naturality square for the actual strict quotient projections. -/
@[simp] theorem projection_quotientMap (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    (T : ParallelCongruence N) (F : Calc.Hom M N) (hF : R.MapsTo T F) :
    R.projection.comp (R.quotientMap T F hF) = F.comp T.projection := by
  exact R.projection_factor (F.comp T.projection) (fun h => Quotient.sound (hF h))

/-- Identity maps preserve any congruence. -/
theorem mapsTo_id (R : ParallelCongruence M) : R.MapsTo R (Calc.Hom.id M) := fun h => h

/-- Compatibility is stable under composition. -/
theorem mapsTo_comp (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    {P : Calc.{u, v, z''} V} (T : ParallelCongruence N) (U : ParallelCongruence P)
    (F : Calc.Hom M N) (G : Calc.Hom N P) (hF : R.MapsTo T F) (hG : T.MapsTo U G) :
    R.MapsTo U (F.comp G) := fun h => hG (hF h)

/-- The induced quotient map preserves identities. -/
@[simp] theorem quotientMap_id (R : ParallelCongruence M) :
    R.quotientMap R (Calc.Hom.id M) R.mapsTo_id = Calc.Hom.id R.quotient := by
  apply Calc.Hom.ext
  intro c a
  induction a using Quotient.inductionOn with
  | _ a => rfl

/-- The induced quotient map preserves composition, with no chosen-representative coherence axiom. -/
theorem quotientMap_comp (R : ParallelCongruence M) {N : Calc.{u, v, z'} V}
    {P : Calc.{u, v, z''} V} (T : ParallelCongruence N) (U : ParallelCongruence P)
    (F : Calc.Hom M N) (G : Calc.Hom N P) (hF : R.MapsTo T F) (hG : T.MapsTo U G) :
    R.quotientMap U (F.comp G) (R.mapsTo_comp T U F G hF hG) =
      (R.quotientMap T F hF).comp (T.quotientMap U G hG) := by
  apply Calc.Hom.ext
  intro c a
  induction a using Quotient.inductionOn with
  | _ a => rfl

end ParallelCongruence
end WitnessedDecompositions
