module

public import WitnessedDecompositions.RawRefinement
public import WitnessedDecompositions.SemanticRefinement
public import WitnessedDecompositions.RefinementLifting

/-!
# Raw/free refinement identification and evaluation functors

B2 under unchanged CompletionContract v0.1,
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
The maps below retain actual forest/tuple data. Their inverse laws use A1's
component-preserving occurrence equivalence. No quotient of arrows is taken.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

universe u v w z
namespace WitnessedDecompositions.RefinementComparison
open CategoryTheory
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}

/-- Read a raw forest at every full-profile occurrence. -/
def rawToFreeArrow {c : Component V} {t u : Tree S c} (f : Raw.Arrow t u) :
    SemanticRefinement.Arrow (Tree.freeCalc S) t u :=
  ⟨(Tree.profileSubstitutionEquiv t).symm f.val, by
    change Tree.profileGraft t ((Tree.profileSubstitutionEquiv t).symm f.val) = u
    rw [Tree.profileGraft_eq_graft, Equiv.apply_symm_apply]
    exact f.property⟩

/-- Recover the exact structural forest from its full-profile tuple. -/
def freeToRawArrow {c : Component V} {t u : Tree S c}
    (f : SemanticRefinement.Arrow (Tree.freeCalc S) t u) : Raw.Arrow t u :=
  ⟨Tree.profileSubstitutionEquiv t f.val, by
    rw [← Tree.profileGraft_eq_graft]
    exact f.property⟩

@[simp] theorem freeToRaw_rawToFree {c : Component V} {t u : Tree S c}
    (f : Raw.Arrow t u) : freeToRawArrow (rawToFreeArrow f) = f := by
  apply Subtype.ext
  exact (Tree.profileSubstitutionEquiv t).apply_symm_apply f.val

@[simp] theorem rawToFree_freeToRaw {c : Component V} {t u : Tree S c}
    (f : SemanticRefinement.Arrow (Tree.freeCalc S) t u) :
    rawToFreeArrow (freeToRawArrow f) = f := by
  apply Subtype.ext
  exact (Tree.profileSubstitutionEquiv t).symm_apply_apply f.val

/-- An explicit bijection of whole retained hom tuples, not merely reachability. -/
def arrowEquiv {c : Component V} (t u : Tree S c) :
    Raw.Arrow t u ≃ SemanticRefinement.Arrow (Tree.freeCalc S) t u where
  toFun := rawToFreeArrow
  invFun := freeToRawArrow
  left_inv := freeToRaw_rawToFree
  right_inv := rawToFree_freeToRaw

/-- The free semantic hom is thin because its complete tuple recovers a unique
raw forest, not because the tuple is erased or quotiented. -/
instance free_hom_subsingleton {c : Component V} (t u : Tree S c) :
    Subsingleton (SemanticRefinement.Arrow (Tree.freeCalc S) t u) :=
  ⟨fun _f _g => (arrowEquiv t u).symm.injective (Subsingleton.elim _ _)⟩

@[simp] theorem rawToFree_id {c : Component V} (t : Tree S c) :
    rawToFreeArrow (Raw.id t) = SemanticRefinement.id (M := Tree.freeCalc S) t := Subsingleton.elim _ _

/-- The two sides are equal as entire tuples. B1's unique forest recovery proves
this equality; both compositions were independently defined by substitution. -/
theorem rawToFree_comp {c : Component V} {t u v : Tree S c}
    (f : Raw.Arrow t u) (g : Raw.Arrow u v) :
    rawToFreeArrow (Raw.comp f g) =
      SemanticRefinement.comp (rawToFreeArrow f) (rawToFreeArrow g) := Subsingleton.elim _ _

@[simp] theorem freeToRaw_id {c : Component V} (t : Tree S c) :
    freeToRawArrow (SemanticRefinement.id t) = Raw.id t := Subsingleton.elim _ _

theorem freeToRaw_comp {c : Component V} {t u v : Tree S c}
    (f : SemanticRefinement.Arrow (Tree.freeCalc S) t u)
    (g : SemanticRefinement.Arrow (Tree.freeCalc S) u v) :
    freeToRawArrow (SemanticRefinement.comp f g) =
      Raw.comp (freeToRawArrow f) (freeToRawArrow g) := Subsingleton.elim _ _

/-- Identity on underlying trees, explicit occurrence conversion on arrows. -/
def rawToFree (S : Signature.{u,v,w} V) (c : Component V) :
    Tree S c ⥤ SemanticRefinement.Object (Tree.freeCalc S) c where
  obj t := ⟨t⟩
  map := rawToFreeArrow
  map_id := rawToFree_id
  map_comp := rawToFree_comp

/-- The inverse functor retains the same underlying tree object. -/
def freeToRaw (S : Signature.{u,v,w} V) (c : Component V) :
    SemanticRefinement.Object (Tree.freeCalc S) c ⥤ Tree S c where
  obj a := a.val
  map := freeToRawArrow
  map_id a := freeToRaw_id a.val
  map_comp := freeToRaw_comp

@[simp] theorem rawToFree_freeToRaw_functor (S : Signature.{u,v,w} V) (c : Component V) :
    rawToFree S c ⋙ freeToRaw S c = 𝟭 (Tree S c) := by
  unfold rawToFree freeToRaw Functor.comp Functor.id
  congr 1
  funext t u f
  exact freeToRaw_rawToFree f

@[simp] theorem freeToRaw_rawToFree_functor (S : Signature.{u,v,w} V) (c : Component V) :
    freeToRaw S c ⋙ rawToFree S c = 𝟭 (SemanticRefinement.Object (Tree.freeCalc S) c) := by
  unfold rawToFree freeToRaw Functor.comp Functor.id
  congr 1
  funext t u f
  exact rawToFree_freeToRaw f

/-- Every strict interpretation of the free calculus acts on actual raw arrows. -/
def rawFunctor {M : Calc.{u,v,z} V} (H : Calc.Hom (Tree.freeCalc S) M)
    (c : Component V) : Tree S c ⥤ SemanticRefinement.Object M c where
  obj t := ⟨H.map t⟩
  map f := SemanticRefinement.mapArrow H (rawToFreeArrow f)
  map_id t := by
    change SemanticRefinement.mapArrow H (rawToFreeArrow (Raw.id t)) =
      SemanticRefinement.id (H.map t)
    rw [rawToFree_id, SemanticRefinement.mapArrow_id]
  map_comp f g := by
    change SemanticRefinement.mapArrow H (rawToFreeArrow (Raw.comp f g)) =
      SemanticRefinement.comp (SemanticRefinement.mapArrow H (rawToFreeArrow f))
        (SemanticRefinement.mapArrow H (rawToFreeArrow g))
    rw [rawToFree_comp, SemanticRefinement.mapArrow_comp]

/-- The raw functor maps precisely the entrywise interpretation of the original
forest after the canonical profile/occurrence conversion. -/
theorem rawFunctor_map_val {M : Calc.{u,v,z} V}
    (H : Calc.Hom (Tree.freeCalc S) M) {c : Component V} {t u : Tree S c}
    (f : Raw.Arrow t u) :
    ((rawFunctor H c).map f).val =
      M.toCollection.reindex (H.profile_map t)
        (H.toHom.onFamily ((Tree.profileSubstitutionEquiv t).symm f.val)) := rfl

/-- Interpretation of arbitrary primitive witnesses induces a raw evaluation functor. -/
def evaluationFunctor (M : Calc.{u,v,z} V) (a : S.Assignment M)
    (c : Component V) : Tree S c ⥤ SemanticRefinement.Object M c :=
  rawFunctor (Tree.extend M a) c

/-- Identity preservation is an equality of complete interpreted tuples. -/
theorem evaluation_map_id (M : Calc.{u,v,z} V) (a : S.Assignment M)
    {c : Component V} (t : Tree S c) :
    (evaluationFunctor M a c).map (Raw.id t) =
      SemanticRefinement.id (Tree.interpret M a t) :=
  (evaluationFunctor M a c).map_id t

/-- Composition preservation is an equality of complete interpreted tuples. -/
theorem evaluation_map_comp (M : Calc.{u,v,z} V) (a : S.Assignment M)
    {c : Component V} {t u v : Tree S c} (f : Raw.Arrow t u) (g : Raw.Arrow u v) :
    (evaluationFunctor M a c).map (Raw.comp f g) =
      SemanticRefinement.comp ((evaluationFunctor M a c).map f)
        ((evaluationFunctor M a c).map g) :=
  (evaluationFunctor M a c).map_comp f g

/-- Automatic hom-injectivity from raw thinness: this theorem deliberately
requires no injectivity of interpretation and makes no object-recovery claim. -/
theorem rawFunctor_map_injective {M : Calc.{u,v,z} V}
    (H : Calc.Hom (Tree.freeCalc S) M) {c : Component V} (t u : Tree S c) :
    Function.Injective (fun f : Raw.Arrow t u => (rawFunctor H c).map f) := by
  intro f g _
  exact Subsingleton.elim f g


/-- Supplied entrywise lifts and equality reflection at the whole produce a
unique raw arrow with that evaluated tuple. The lift hypotheses mention no
raw endpoint equality; that equality is derived by liftArrow_of_family. -/
theorem unique_raw_lift_of_family {M : Calc.{u,v,z} V}
    (H : Calc.Hom (Tree.freeCalc S) M) {c : Component V}
    (hinj : Function.Injective (@H.map c)) {t u : Tree S c}
    (g : SemanticRefinement.Arrow M (H.map t) (H.map u))
    (f : (Tree.collection S).Family (Tree.frontier t))
    (hlift : M.toCollection.reindex (H.profile_map t) (H.toHom.onFamily f) = g.val) :
    ∃! f' : Raw.Arrow t u, (rawFunctor H c).map f' = g := by
  obtain ⟨f',hf'⟩ := SemanticRefinement.liftArrow_of_family H hinj g f hlift
  refine ⟨freeToRawArrow f', ?_, ?_⟩
  · change SemanticRefinement.mapArrow H (rawToFreeArrow (freeToRawArrow f')) = g
    rw [rawToFree_freeToRaw]
    exact hf'
  · intro other _
    exact Subsingleton.elim _ _

end WitnessedDecompositions.RefinementComparison
