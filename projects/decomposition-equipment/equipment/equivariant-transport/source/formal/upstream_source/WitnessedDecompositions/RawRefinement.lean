module

public import WitnessedDecompositions.FreeCalculus

/-!
# Raw leaf-graft refinements

B1 under CompletionContract v0.1, SHA256
47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
Arrows retain the actual typed forest. Thinness is a theorem, not a definition.
All interfaces, components and signatures are arbitrary; nullaries are included.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

universe u v w z
namespace WitnessedDecompositions
namespace Tree
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}

/-- A retained source tree permits unique recovery of the whole graft forest. -/
theorem graft_injective {c : Component V} (t : Tree S c) :
    Function.Injective (graft t) := by
  induction t with
  | leaf c => intro σ τ h; exact h
  | node g ch ih =>
    intro σ τ h
    have hc : (fun i => graft (ch i) (σ i)) = (fun i => graft (ch i) (τ i)) := by
      injection h
    funext i
    exact ih i (congrFun hc i)

/-- A nontrivial leaf expansion can never be undone by more leaf expansion. -/
theorem graft_no_cycle {c : Component V} (t : Tree S c) (σ : Substitution t)
    (τ : Substitution (graft t σ)) (h : graft (graft t σ) τ = t) :
    graft t σ = t := by
  induction t with
  | leaf c =>
    cases σ with
    | leaf c => rfl
    | node g ch => cases h
  | node g ch ih =>
    have hc : (fun i => graft (graft (ch i) (σ i)) (τ i)) = ch := by
      injection h
    change Tree.node g _ = Tree.node g _
    congr 1
    funext i
    exact ih i (σ i) (τ i) (congrFun hc i)

/-- Insert a nested leaf occurrence into its exact original source occurrence. -/
def graftLeaf : {c : Component V} → (t : Tree S c) → (σ : Substitution t) →
    (l : Leaf t) → Leaf (atLeaf t σ l) → Leaf (graft t σ)
  | _, .leaf _, _ => fun _ k => k
  | _, .node _ ch, σ => fun ⟨i,l⟩ k => ⟨i, graftLeaf (ch i) (σ i) l k⟩

/-- Recover the original and inserted occurrences of a final graft leaf. -/
def ungraftLeaf : {c : Component V} → (t : Tree S c) → (σ : Substitution t) →
    Leaf (graft t σ) → (l : Leaf t) × Leaf (atLeaf t σ l)
  | _, .leaf _, _ => fun k => ⟨(),k⟩
  | _, .node _ ch, σ => fun ⟨i,k⟩ =>
      let x := ungraftLeaf (ch i) (σ i) k
      ⟨⟨i,x.1⟩,x.2⟩

@[simp] theorem ungraftLeaf_graftLeaf {c : Component V} (t : Tree S c)
    (σ : Substitution t) (l : Leaf t) (k : Leaf (atLeaf t σ l)) :
    ungraftLeaf t σ (graftLeaf t σ l k) = ⟨l,k⟩ := by
  induction t with
  | leaf c => cases l; rfl
  | node g ch ih =>
    rcases l with ⟨i,l⟩
    change (fun x : (j : Leaf (ch i)) × Leaf (atLeaf (ch i) (σ i) j) =>
      (⟨⟨i,x.1⟩,x.2⟩ : (j : Leaf (Tree.node g ch)) × Leaf (atLeaf (Tree.node g ch) σ j)))
        (ungraftLeaf (ch i) (σ i) (graftLeaf (ch i) (σ i) l k)) = _
    rw [ih]

@[simp] theorem graftLeaf_ungraftLeaf {c : Component V} (t : Tree S c)
    (σ : Substitution t) (k : Leaf (graft t σ)) :
    graftLeaf t σ (ungraftLeaf t σ k).1 (ungraftLeaf t σ k).2 = k := by
  induction t with
  | leaf c => rfl
  | node g ch ih =>
    rcases k with ⟨i,k⟩
    exact congrArg (Sigma.mk i) (ih i (σ i) k)

/-- The actual component-preserving occurrence bijection for every forest. -/
def graftLeafEquiv {c : Component V} (t : Tree S c) (σ : Substitution t) :
    Leaf (graft t σ) ≃ (l : Leaf t) × Leaf (atLeaf t σ l) where
  toFun := ungraftLeaf t σ
  invFun x := graftLeaf t σ x.1 x.2
  left_inv := graftLeaf_ungraftLeaf t σ
  right_inv x := ungraftLeaf_graftLeaf t σ x.1 x.2

/-- Nested graft positions preserve both endpoints and the actual component edge. -/
theorem graftLeaf_component {c : Component V} (t : Tree S c) (σ : Substitution t)
    (l : Leaf t) (k : Leaf (atLeaf t σ l)) :
    leafComponent (graft t σ) (graftLeaf t σ l k) =
      leafComponent (atLeaf t σ l) k := by
  induction t with
  | leaf c => rfl
  | node g ch ih => exact ih l.1 (σ l.1) l.2 k

theorem graftLeafEquiv_component {c : Component V} (t : Tree S c)
    (σ : Substitution t) (k : Leaf (graft t σ)) :
    leafComponent (graft t σ) k =
      leafComponent (atLeaf t σ (graftLeafEquiv t σ k).1) (graftLeafEquiv t σ k).2 := by
  exact (congrArg (leafComponent (graft t σ)) (graftLeaf_ungraftLeaf t σ k).symm).trans
    (graftLeaf_component t σ _ _)

/-- The second-layer forest restricted to the replacement at one original leaf. -/
def innerAtLeaf : {c : Component V} → (t : Tree S c) → (σ : Substitution t) →
    (τ : Substitution (graft t σ)) → (l : Leaf t) → Substitution (atLeaf t σ l)
  | _, .leaf _, _, τ => fun _ => τ
  | _, .node _ ch, σ, τ => fun ⟨i,l⟩ => innerAtLeaf (ch i) (σ i) (τ i) l

/-- Forest composition acts independently at each original occurrence. -/
theorem atLeaf_compose {c : Component V} (t : Tree S c) (σ : Substitution t)
    (τ : Substitution (graft t σ)) (l : Leaf t) :
    atLeaf t (compose t σ τ) l =
      graft (atLeaf t σ l) (innerAtLeaf t σ τ l) := by
  induction t with
  | leaf c => rfl
  | node g ch ih => exact ih l.1 (σ l.1) (τ l.1) l.2

/-- The restricted forest reads exactly the second-stage tuple via the nested
occurrence map, including the necessary full-component transport. -/
theorem atLeaf_innerAtLeaf {c : Component V} (t : Tree S c) (σ : Substitution t)
    (τ : Substitution (graft t σ)) (l : Leaf t) (k : Leaf (atLeaf t σ l)) :
    atLeaf (atLeaf t σ l) (innerAtLeaf t σ τ l) k =
      Path.occurrenceTransport (Tree S) (graftLeaf_component t σ l k)
        (atLeaf (graft t σ) τ (graftLeaf t σ l k)) := by
  induction t with
  | leaf c => rfl
  | node g ch ih => exact ih l.1 (σ l.1) (τ l.1) l.2 k

/-- Canonical occurrence transport along equality of retained trees. -/
def leafCast {c : Component V} {t u : Tree S c} (h : t = u) : Leaf t → Leaf u :=
  h ▸ id

@[simp] theorem leafCast_rfl {c : Component V} (t : Tree S c) (l : Leaf t) :
    leafCast (rfl : t = t) l = l := rfl

theorem leafCast_node (g : S.Generator)
    {ch dh : ∀ i, Tree S (S.argument g i)} (e : ch = dh)
    (i : Path.Slot (S.input g)) (l : Leaf (ch i)) :
    leafCast (congrArg (Tree.node g) e) ⟨i,l⟩ =
      ⟨i,leafCast (congrFun e i) l⟩ := by
  cases e
  rfl

/-- A three-level nested occurrence, inserted through the left-associated graft.
The domain retains its original leaf, the next leaf, and its third-stage leaf. -/
def graftLeafTriple : {c : Component V} → (t : Tree S c) → (σ : Substitution t) →
    (τ : Substitution (graft t σ)) → (l : Leaf t) → (k : Leaf (atLeaf t σ l)) →
    Leaf (atLeaf (atLeaf t σ l) (innerAtLeaf t σ τ l) k) →
    Leaf (graft (graft t σ) τ)
  | _, .leaf _, σ, τ => fun _ k m => graftLeaf σ τ k m
  | _, .node _ ch, σ, τ => fun ⟨i,l⟩ k m =>
      ⟨i,graftLeafTriple (ch i) (σ i) (τ i) l k m⟩

/-- Read a third-stage leaf at the actual second-stage source occurrence.
This recursive map resolves precisely the component transport exposed by
atLeaf_innerAtLeaf; it never selects a leaf by its label. -/
def innerLeaf : {c : Component V} → (t : Tree S c) → (σ : Substitution t) →
    (τ : Substitution (graft t σ)) → (l : Leaf t) → (k : Leaf (atLeaf t σ l)) →
    Leaf (atLeaf (atLeaf t σ l) (innerAtLeaf t σ τ l) k) →
    Leaf (atLeaf (graft t σ) τ (graftLeaf t σ l k))
  | _, .leaf _, _, _ => fun _ _ m => m
  | _, .node _ ch, σ, τ => fun ⟨i,l⟩ k m => innerLeaf (ch i) (σ i) (τ i) l k m

/-- The left-associated triple map is the actual composite of the two graft
occurrence maps, with precisely the required third-leaf reindexing. -/
theorem graftLeafTriple_eq {c : Component V} (t : Tree S c) (σ : Substitution t)
    (τ : Substitution (graft t σ)) (l : Leaf t) (k : Leaf (atLeaf t σ l))
    (m : Leaf (atLeaf (atLeaf t σ l) (innerAtLeaf t σ τ l) k)) :
    graftLeafTriple t σ τ l k m =
      graftLeaf (graft t σ) τ (graftLeaf t σ l k) (innerLeaf t σ τ l k m) := by
  induction t with
  | leaf c => rfl
  | node g ch ih =>
    rcases l with ⟨i,l⟩
    exact congrArg (Sigma.mk i) (ih i (σ i) (τ i) l k m)

/-- All three occurrence coordinates survive reassociation, not merely their
component labels or their total number. -/
theorem graftLeaf_assoc {c : Component V} (t : Tree S c) (σ : Substitution t)
    (τ : Substitution (graft t σ)) (l : Leaf t) (k : Leaf (atLeaf t σ l))
    (m : Leaf (atLeaf (atLeaf t σ l) (innerAtLeaf t σ τ l) k)) :
    leafCast (graft_assoc t σ τ) (graftLeafTriple t σ τ l k m) =
      graftLeaf t (compose t σ τ) l
        (leafCast (atLeaf_compose t σ τ l).symm
          (graftLeaf (atLeaf t σ l) (innerAtLeaf t σ τ l) k m)) := by
  induction t with
  | leaf c => rfl
  | node g ch ih =>
    rcases l with ⟨i,l⟩
    let he : (fun i => graft (graft (ch i) (σ i)) (τ i)) =
        (fun i => graft (ch i) (compose (ch i) (σ i) (τ i))) :=
      funext (fun i => graft_assoc (ch i) (σ i) (τ i))
    exact (leafCast_node g he i (graftLeafTriple (ch i) (σ i) (τ i) l k m)).trans
      (congrArg (Sigma.mk i) (ih i (σ i) (τ i) l k m))

/-- The structural forest reads precisely the prescribed full-profile family
through A1's component-preserving frontier occurrence equivalence. -/
theorem atLeaf_profileSubstitutionEquiv {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t)) (l : Leaf t) :
    atLeaf t (profileSubstitutionEquiv t f) l =
      Path.occurrenceTransport (Tree S) (frontierLeafEquiv_symm_component t l)
        (f ((frontierLeafEquiv t).symm l)) := by
  exact atLeaf_fromLeaves t (leafFamilyEquiv (Tree S) t f) l

/-- Reading every final profile slot as a nested leaf is an actual equivalence.
Combined with atLeaf_profileSubstitutionEquiv this is the full typed bridge
between prescribed profile forests and structural forest data. -/
def profileGraftLeafEquiv {c : Component V} (t : Tree S c) (σ : Substitution t) :
    Path.Slot (frontier (graft t σ)) ≃ (l : Leaf t) × Leaf (atLeaf t σ l) :=
  (frontierLeafEquiv (graft t σ)).trans (graftLeafEquiv t σ)

/-- The full profile bridge preserves the complete directed component. -/
theorem profileGraftLeafEquiv_component {c : Component V} (t : Tree S c)
    (σ : Substitution t) (i : Path.Slot (frontier (graft t σ))) :
    Path.componentAt (frontier (graft t σ)) i =
      leafComponent (atLeaf t σ (profileGraftLeafEquiv t σ i).1)
        (profileGraftLeafEquiv t σ i).2 :=
  (frontierLeafEquiv_component (graft t σ) i).trans
    (graftLeafEquiv_component t σ (frontierLeafEquiv (graft t σ) i))

/-- Collect values at leaves in intrinsic left-to-right tree order. -/
def collectLeaves {α : Type z} : {c : Component V} → (t : Tree S c) →
    (Leaf t → List α) → List α
  | _, .leaf _, f => f ()
  | _, .node g ch, f => Path.collect (S.input g) (fun i => collectLeaves (ch i) (fun l => f ⟨i,l⟩))

/-- A1's frontier-leaf map preserves the exact ordered traversal, not just
labels. The node step is precisely the ordered Path.slotExpand correspondence. -/
theorem collect_frontierLeafEquiv {α : Type z} {c : Component V}
    (t : Tree S c) (f : Leaf t → List α) :
    Path.collect (frontier t) (fun i => f (frontierLeafEquiv t i)) = collectLeaves t f := by
  induction t with
  | leaf c => rfl
  | node g ch ih =>
    change Path.collect (Path.expand (S.input g) (fun i => frontier (ch i))) _ = _
    rw [Path.collect_expand_slots]
    change Path.collect (S.input g) _ = Path.collect (S.input g) _
    congr 1
    funext i
    have he (j : Path.Slot (frontier (ch i))) :
        frontierLeafEquiv (.node g ch)
          ((Path.slotExpand (S.input g) (fun i => frontier (ch i))).symm ⟨i,j⟩) =
          ⟨i,frontierLeafEquiv (ch i) j⟩ := by
      exact congrArg
        (fun x : (i : Path.Slot (S.input g)) × Path.Slot (frontier (ch i)) =>
          (⟨x.1,frontierLeafEquiv (ch x.1) x.2⟩ : Leaf (.node g ch)))
        ((Path.slotExpand (S.input g) (fun i => frontier (ch i))).apply_symm_apply ⟨i,j⟩)
    calc
      _ = Path.collect (frontier (ch i)) (fun j => f ⟨i,frontierLeafEquiv (ch i) j⟩) := by
        congr 1
        funext j
        exact congrArg f (he j)
      _ = _ := ih i (fun l => f ⟨i,l⟩)

/-- The graft occurrence bijection is ordered concatenation of the actual
replacement traversals, including empty traversals of nullary replacements. -/
theorem collect_graftLeaf {α : Type z} {c : Component V} (t : Tree S c)
    (σ : Substitution t) (f : Leaf (graft t σ) → List α) :
    collectLeaves (graft t σ) f = collectLeaves t
      (fun l => collectLeaves (atLeaf t σ l) (fun k => f (graftLeaf t σ l k))) := by
  induction t with
  | leaf c => rfl
  | node g ch ih =>
    change Path.collect (S.input g) _ = Path.collect (S.input g) _
    congr 1
    funext i
    exact ih i (σ i) (fun k => f ⟨i,k⟩)

/-- The profile/structural occurrence bridge agrees with A1's ordered expansion
on every list-valued test, hence cannot permute even identically labelled leaves. -/
theorem collect_profileGraftLeaf {α : Type z} {c : Component V} (t : Tree S c)
    (σ : Substitution t) (f : Leaf (graft t σ) → List α) :
    Path.collect (frontier (graft t σ))
      (fun i => f (frontierLeafEquiv (graft t σ) i)) =
        collectLeaves t (fun l => collectLeaves (atLeaf t σ l)
          (fun k => f (graftLeaf t σ l k))) :=
  (collect_frontierLeafEquiv _ _).trans (collect_graftLeaf t σ f)

/-- Simultaneous transport of a source and its forest leaves the resulting tree unchanged. -/
theorem graft_cast {c : Component V} {t u : Tree S c} (h : t = u) (σ : Substitution t) :
    graft u (h ▸ σ) = graft t σ := by
  cases h
  rfl

/-- Profile-indexed composition and structural forest composition are literally
the same retained forest; the profile-side split is A1's slotExpand split. -/
theorem profileSubstitutionEquiv_compose {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t))
    (h : (collection S).Family (frontier (profileGraft t f))) :
    profileSubstitutionEquiv t ((calcData S).composeFamily t f h) =
      compose t (profileSubstitutionEquiv t f)
        ((profileGraft_eq_graft t f) ▸ profileSubstitutionEquiv (profileGraft t f) h) := by
  apply graft_injective t
  rw [← profileGraft_eq_graft, ← profileGraft_assoc]
  rw [← graft_assoc]
  rw [graft_cast]
  exact profileGraft_eq_graft _ _

end Tree

namespace Raw
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u,v,w} V}

/-- Actual arrows retain every tree in the occurrence-indexed forest. -/
def Arrow {c : Component V} (t u : Tree S c) :=
  {σ : Tree.Substitution t // Tree.graft t σ = u}

/-- The identity forest, not an identity execution event. -/
def id {c : Component V} (t : Tree S c) : Arrow t t :=
  ⟨Tree.identity t, Tree.graft_identity t⟩

/-- Composition by the actual typed forest substitution. -/
def comp {c : Component V} {t u v : Tree S c} (f : Arrow t u) (g : Arrow u v) :
    Arrow t v := by
  rcases f with ⟨σ,hσ⟩
  subst u
  exact ⟨Tree.compose t σ g.val, (Tree.graft_assoc t σ g.val).symm.trans g.property⟩

/-- Composition exposes the retained forest and the sole endpoint transport. -/
theorem comp_val {c : Component V} {t u v : Tree S c} (f : Arrow t u) (g : Arrow u v) :
    (comp f g).val = Tree.compose t f.val (f.property.symm ▸ g.val) := by
  rcases f with ⟨σ,hσ⟩
  subst u
  rfl

/-- Forest recovery, rather than erasure of the arrow, proves raw thinness. -/
instance hom_subsingleton {c : Component V} (t u : Tree S c) : Subsingleton (Arrow t u) :=
  ⟨fun f g => Subtype.ext (Tree.graft_injective t (f.property.trans g.property.symm))⟩

@[simp] theorem id_comp {c : Component V} {t u : Tree S c} (f : Arrow t u) :
    comp (id t) f = f := Subsingleton.elim _ _

@[simp] theorem comp_id {c : Component V} {t u : Tree S c} (f : Arrow t u) :
    comp f (id u) = f := Subsingleton.elim _ _

theorem comp_assoc {c : Component V} {t u v x : Tree S c}
    (f : Arrow t u) (g : Arrow u v) (h : Arrow v x) :
    comp (comp f g) h = comp f (comp g h) := Subsingleton.elim _ _

/-- The raw category is genuinely a thin category of retained forests. -/
instance {c : Component V} : CategoryTheory.Category (Tree S c) where
  Hom := Arrow
  id := id
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := comp_assoc

/-- Refinements in both directions force equality of literal presentation trees. -/
theorem antisymm {c : Component V} {t u : Tree S c} (f : Arrow t u) (g : Arrow u t) : t = u := by
  rcases f with ⟨σ,hσ⟩
  subst u
  exact (Tree.graft_no_cycle t σ g.val g.property).symm

/-- Reachability is a consequence of actual arrows, not their replacement. -/
def Refines {c : Component V} (t u : Tree S c) : Prop := Nonempty (Arrow t u)

theorem refines_refl {c : Component V} (t : Tree S c) : Refines t t := ⟨id t⟩

theorem refines_trans {c : Component V} {t u v : Tree S c} :
    Refines t u → Refines u v → Refines t v := by
  rintro ⟨f⟩ ⟨g⟩
  exact ⟨comp f g⟩

theorem refines_antisymm {c : Component V} {t u : Tree S c} :
    Refines t u → Refines u t → t = u := by
  rintro ⟨f⟩ ⟨g⟩
  exact antisymm f g

/-- The raw category's underlying reachability is a genuine partial order.
The structure is named rather than installed globally to avoid changing how
unrelated clients order trees. Its relation is inhabited actual forest arrows. -/
@[instance_reducible] def partialOrder {c : Component V} : PartialOrder (Tree S c) where
  le := Refines
  le_refl := refines_refl
  le_trans := fun _ _ _ => refines_trans
  le_antisymm := fun _ _ => refines_antisymm

end Raw
end WitnessedDecompositions
