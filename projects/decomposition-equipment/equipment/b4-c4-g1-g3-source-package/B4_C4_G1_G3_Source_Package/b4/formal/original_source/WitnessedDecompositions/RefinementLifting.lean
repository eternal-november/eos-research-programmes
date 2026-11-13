module

public import WitnessedDecompositions.SemanticRefinement

/-!
# Explicit sufficient hypotheses for lifting semantic arrows

Contract v0.1 SHA256 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
Endpoint equality is derived from injectivity of the operation interpretation.
The supplied lifts concern individual tuple entries, not refinement endpoints.
-/
@[expose] public section
universe u v w w'
namespace WitnessedDecompositions.SemanticRefinement
variable {V : Type u} [Quiver.{v} V]
variable {M : Calc.{u,v,w} V} {N : Calc.{u,v,w'} V} {c : Component V}

/-- Entrywise operation lifts plus equality reflection at the fixed whole
produce an actual arrow; no endpoint assertion is hidden in the lift premise. -/
theorem liftArrow_of_family (H : Calc.Hom M N)
    (hinj : Function.Injective (@H.map c)) {a b : M.Op c}
    (g : Arrow N (H.map a) (H.map b))
    (f : M.toCollection.Family (M.profile a))
    (hlift : N.toCollection.reindex (H.profile_map a) (H.toHom.onFamily f) = g.val) :
    ∃ f' : Arrow M a b, mapArrow H f' = g := by
  have hf : M.subst a f = b := hinj (by
    rw [H.map_subst, hlift]
    exact g.property)
  refine ⟨⟨f,hf⟩, ?_⟩
  apply Subtype.ext
  exact hlift

/-- Surjectivity on individual operation carriers is sufficient for tuple
liftability. Standard choice is used only to collect these entrywise lifts. -/
theorem mapArrow_surjective_of_operation_lifts (H : Calc.Hom M N)
    (hinj : Function.Injective (@H.map c))
    (hsurj : ∀ d : Component V, Function.Surjective (@H.map d))
    {a b : M.Op c} : Function.Surjective (@mapArrow _ _ M c N H a b) := by
  classical
  intro g
  let target : N.toCollection.Family (M.profile a) :=
    N.toCollection.reindex (H.profile_map a).symm g.val
  have h : ∀ i : Path.Slot (M.profile a),
      ∃ x : M.Op (Path.componentAt (M.profile a) i), H.map x = target i :=
    fun i => hsurj _ _
  choose f hf using h
  apply liftArrow_of_family H hinj g f
  have hfamily : H.toHom.onFamily f = target := funext hf
  rw [hfamily]
  dsimp only [target]
  rw [Collection.reindex_comp, Collection.reindex_refl]

/-- Equality reflection and operation lifts give a bijection on each fixed
semantic hom-set. This does not assume categorical fullness or faithfulness. -/
theorem mapArrow_bijective_of_operation_bijective (H : Calc.Hom M N)
    (hbij : ∀ d : Component V, Function.Bijective (@H.map d))
    {a b : M.Op c} : Function.Bijective (@mapArrow _ _ M c N H a b) :=
  ⟨mapArrow_injective H (fun d => (hbij d).1),
    mapArrow_surjective_of_operation_lifts H (hbij c).1 (fun d => (hbij d).2)⟩

end WitnessedDecompositions.SemanticRefinement
