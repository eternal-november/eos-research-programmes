module

public import WitnessedDecompositions.Core
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Sigma

set_option backward.isDefEq.respectTransparency false
@[expose] public section

universe u v z z'
namespace WitnessedDecompositions.Path
variable {V : Type u} [Quiver.{v} V]

/-- The canonical left-to-right occurrence correspondence for concatenation. -/
def slotComp {a b : V} (p : Quiver.Path a b) :
    {c : V} → (q : Quiver.Path b c) → Slot (p.comp q) ≃ (Slot p ⊕ Slot q)
  | _, .nil =>
    { toFun := Sum.inl
      invFun := fun i => match i with | .inl j => j | .inr j => nomatch j
      left_inv := fun _ => rfl
      right_inv := by rintro (i | i); rfl; exact nomatch i }
  | _, .cons q _ =>
    (Equiv.sumCongr (slotComp p q) (Equiv.refl Unit)).trans (Equiv.sumAssoc _ _ _)

/-- Component labels in the ordered sum of two path occurrence sets. -/
def compComponent {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    Slot p ⊕ Slot q → Component V := Sum.elim (componentAt p) (componentAt q)

@[simp] theorem componentAt_slotComp {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (i : Slot (p.comp q)) :
    componentAt (p.comp q) i = compComponent p q (slotComp p q i) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    cases i with
    | inl i =>
      change componentAt (p.comp q) i = _
      rw [ih]
      change compComponent p q (slotComp p q i) =
        Sum.elim (componentAt p) (componentAt (q.cons e))
          (Sum.elim Sum.inl (fun j => Sum.inr (Sum.inl j)) (slotComp p q i))
      cases slotComp p q i <;> rfl
    | inr i => cases i; rfl

@[simp] theorem componentAt_slotComp_symm {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (i : Slot p ⊕ Slot q) :
    componentAt (p.comp q) ((slotComp p q).symm i) = compComponent p q i := by
  simpa only [Equiv.apply_symm_apply] using componentAt_slotComp p q ((slotComp p q).symm i)

/-- The canonical correspondence for the occurrences of a simultaneous expansion. -/
def slotExpand {a : V} : {b : V} → (p : Quiver.Path a b) →
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target) →
    Slot (expand p f) ≃ (Σ i : Slot p, Slot (f i))
  | _, .nil, _ =>
    { toFun := fun i => nomatch i
      invFun := fun i => nomatch i.1
      left_inv := fun i => nomatch i
      right_inv := fun i => nomatch i.1 }
  | _, .cons p _, f =>
    (slotComp (expand p (fun i => f (.inl i))) (f (.inr ()))).trans
      { toFun := fun i => match i with
          | .inl j => let k := slotExpand p (fun i => f (.inl i)) j
                     ⟨.inl k.1, k.2⟩
          | .inr j => ⟨.inr (), j⟩
        invFun := fun i => match i with
          | ⟨.inl j, k⟩ => .inl ((slotExpand p (fun i => f (.inl i))).symm ⟨j, k⟩)
          | ⟨.inr (), k⟩ => .inr k
        left_inv := by
          rintro (j | j)
          · change Sum.inl ((slotExpand p _).symm (slotExpand p _ j)) = _
            rw [Equiv.symm_apply_apply]
          · rfl
        right_inv := by
          rintro ⟨j | ⟨⟩, k⟩
          · dsimp only
            have h := (slotExpand p (fun i => f (.inl i))).apply_symm_apply ⟨j, k⟩
            exact congrArg (fun x => (⟨Sum.inl x.1, x.2⟩ : Σ i, Slot (f i))) h
          · rfl }

@[simp] theorem slotExpand_cons_apply {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (f : ∀ i : Slot (p.cons e), Quiver.Path (componentAt (p.cons e) i).source
      (componentAt (p.cons e) i).target) (i : Slot (expand (p.cons e) f)) :
    slotExpand (p.cons e) f i =
      match slotComp (expand p (fun i => f (.inl i))) (f (.inr ())) i with
      | .inl j => ⟨.inl (slotExpand p (fun i => f (.inl i)) j).1,
          (slotExpand p (fun i => f (.inl i)) j).2⟩
      | .inr j => ⟨.inr (), j⟩ := by
  rw [slotExpand]
  erw [Equiv.trans_apply]
  cases slotComp (expand p (fun i => f (.inl i))) (f (.inr ())) i <;> rfl

@[simp] theorem componentAt_slotExpand {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (i : Slot (expand p f)) :
    componentAt (expand p f) i =
      componentAt (f (slotExpand p f i).1) (slotExpand p f i).2 := by
  induction p with
  | nil => exact nomatch i
  | cons p e ih =>
    change componentAt ((expand p (fun i => f (.inl i))).comp (f (.inr ()))) i = _
    erw [componentAt_slotComp]
    erw [slotExpand_cons_apply]
    generalize h : slotComp (expand p (fun i => f (.inl i))) (f (.inr ())) i = j
    cases j with
    | inl j =>
      simpa only [compComponent, Sum.elim_inl] using
        ih (fun i => f (.inl i)) j
    | inr j => rfl

@[simp] theorem componentAt_slotExpand_symm {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (i : Σ j : Slot p, Slot (f j)) :
    componentAt (expand p f) ((slotExpand p f).symm i) = componentAt (f i.1) i.2 := by
  exact (componentAt_slotExpand p f ((slotExpand p f).symm i)).trans
    (congrArg (fun x : Σ j, Slot (f j) => componentAt (f x.1) x.2)
      ((slotExpand p f).apply_symm_apply i))

/-- Transport a component-indexed value without making any choice of occurrences. -/
def occurrenceTransport (F : Component V → Sort z) {c d : Component V}
    (h : c = d) (x : F c) : F d := h ▸ x

@[simp] theorem occurrenceTransport_rfl (F : Component V → Sort z) {c : Component V}
    (x : F c) : occurrenceTransport F rfl x = x := rfl

/-- Restrict a component-indexed family to the left input of a concatenation. -/
def compLeftFamily (F : Component V → Sort z) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c)
    (h : ∀ i : Slot (p.comp q), F (componentAt (p.comp q) i))
    (i : Slot p) : F (componentAt p i) :=
  occurrenceTransport F (componentAt_slotComp_symm p q (.inl i))
    (h ((slotComp p q).symm (.inl i)))

/-- Restrict a component-indexed family to the right input of a concatenation. -/
def compRightFamily (F : Component V → Sort z) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c)
    (h : ∀ i : Slot (p.comp q), F (componentAt (p.comp q) i))
    (i : Slot q) : F (componentAt q i) :=
  occurrenceTransport F (componentAt_slotComp_symm p q (.inr i))
    (h ((slotComp p q).symm (.inr i)))

@[simp] theorem compLeftFamily_nil (F : Component V → Sort z) {a b : V}
    (p : Quiver.Path a b) (h : ∀ i : Slot p, F (componentAt p i)) :
    compLeftFamily F p .nil h = h := rfl

@[simp] theorem compLeftFamily_cons (F : Component V → Sort z) {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (e : c ⟶ d)
    (h : ∀ i : Slot (p.comp (q.cons e)), F (componentAt (p.comp (q.cons e)) i)) :
    compLeftFamily F p (q.cons e) h = compLeftFamily F p q (fun i => h (.inl i)) := rfl

@[simp] theorem compRightFamily_cons_inl (F : Component V → Sort z) {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (e : c ⟶ d)
    (h : ∀ i : Slot (p.comp (q.cons e)), F (componentAt (p.comp (q.cons e)) i))
    (i : Slot q) :
    compRightFamily F p (q.cons e) h (.inl i) =
      compRightFamily F p q (fun i => h (.inl i)) i := rfl

@[simp] theorem compRightFamily_cons_inr (F : Component V → Sort z) {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (e : c ⟶ d)
    (h : ∀ i : Slot (p.comp (q.cons e)), F (componentAt (p.comp (q.cons e)) i)) :
    compRightFamily F p (q.cons e) h (.inr ()) = h (.inr ()) := rfl

/-- Expanding a concatenation is concatenating the two independently restricted expansions. -/
theorem expand_comp {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (h : ∀ i : Slot (p.comp q),
      Quiver.Path (componentAt (p.comp q) i).source (componentAt (p.comp q) i).target) :
    expand (p.comp q) h =
      (expand p (compLeftFamily (fun c => Quiver.Path c.source c.target) p q h)).comp
      (expand q (compRightFamily (fun c => Quiver.Path c.source c.target) p q h)) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    change (expand (p.comp q) (fun i => h (.inl i))).comp (h (.inr ())) = _
    rw [ih]
    simp only [expand, compLeftFamily_cons, compRightFamily_cons_inl,
      compRightFamily_cons_inr, Quiver.Path.comp_assoc]

/-- Pull a family on an expanded path back to any particular inserted occurrence. -/
def expandFamily (F : Component V → Sort z) {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f), F (componentAt (expand p f) i))
    (i : Slot p) (j : Slot (f i)) : F (componentAt (f i) j) :=
  occurrenceTransport F (componentAt_slotExpand_symm p f ⟨i, j⟩)
    (h ((slotExpand p f).symm ⟨i, j⟩))

@[simp] theorem occurrenceTransport_trans (F : Component V → Sort z)
    {c d e : Component V} (h : c = d) (k : d = e) (x : F c) :
    occurrenceTransport F k (occurrenceTransport F h x) =
      occurrenceTransport F (h.trans k) x := by cases h; cases k; rfl

@[simp] theorem slotExpand_cons_symm_inl {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (f : ∀ i : Slot (p.cons e), Quiver.Path (componentAt (p.cons e) i).source
      (componentAt (p.cons e) i).target) (i : Slot p) (j : Slot (f (.inl i))) :
    (slotExpand (p.cons e) f).symm ⟨.inl i, j⟩ =
      (slotComp (expand p (fun i => f (.inl i))) (f (.inr ()))).symm
        (.inl ((slotExpand p (fun i => f (.inl i))).symm ⟨i, j⟩)) := rfl

@[simp] theorem slotExpand_cons_symm_inr {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (f : ∀ i : Slot (p.cons e), Quiver.Path (componentAt (p.cons e) i).source
      (componentAt (p.cons e) i).target) (j : Slot (f (.inr ()))) :
    (slotExpand (p.cons e) f).symm ⟨.inr (), j⟩ =
      (slotComp (expand p (fun i => f (.inl i))) (f (.inr ()))).symm (.inr j) := rfl

@[simp] theorem expandFamily_cons_inl (F : Component V → Sort z)
    {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (f : ∀ i : Slot (p.cons e), Quiver.Path (componentAt (p.cons e) i).source
      (componentAt (p.cons e) i).target)
    (h : ∀ i : Slot (expand (p.cons e) f), F (componentAt (expand (p.cons e) f) i))
    (i : Slot p) (j : Slot (f (.inl i))) :
    expandFamily F (p.cons e) f h (.inl i) j =
      expandFamily F p (fun i => f (.inl i))
        (compLeftFamily F (expand p (fun i => f (.inl i))) (f (.inr ())) h) i j := by
  unfold expandFamily compLeftFamily
  rw [occurrenceTransport_trans]
  rfl

@[simp] theorem expandFamily_cons_inr (F : Component V → Sort z)
    {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (f : ∀ i : Slot (p.cons e), Quiver.Path (componentAt (p.cons e) i).source
      (componentAt (p.cons e) i).target)
    (h : ∀ i : Slot (expand (p.cons e) f), F (componentAt (expand (p.cons e) f) i))
    (j : Slot (f (.inr ()))) :
    expandFamily F (p.cons e) f h (.inr ()) j =
      compRightFamily F (expand p (fun i => f (.inl i))) (f (.inr ())) h j := rfl

/-- Associativity with the second layer reindexed by the canonical occurrence correspondence. -/
theorem expand_assoc {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target) :
    expand (expand p f) h = expand p (fun i =>
      expand (f i) (expandFamily (fun c => Quiver.Path c.source c.target) p f h i)) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change expand ((expand p (fun i => f (.inl i))).comp (f (.inr ()))) h = _
    rw [expand_comp, ih]
    simp only [expand]
    congr 1
    · congr 1
      funext i
      congr 1
      funext j
      exact (expandFamily_cons_inl (fun c => Quiver.Path c.source c.target) p e f h i j).symm

/-- Ordered collection across the occurrence equivalence for concatenation. -/
theorem collect_comp_slots {α : Type z} {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) (h : Slot (p.comp q) → List α) :
    collect (p.comp q) h =
      collect p (fun i => h ((slotComp p q).symm (.inl i))) ++
      collect q (fun i => h ((slotComp p q).symm (.inr i))) := by
  induction q with
  | nil => simp only [collect, List.append_nil]; rfl
  | cons q e ih =>
    change collect (p.comp q) (fun i => h (.inl i)) ++ h (.inr ()) = _
    rw [ih]
    simp only [collect, List.append_assoc]
    rfl

/-- Ordered collection across expansion. In particular the bijection never permutes occurrences. -/
theorem collect_expand_slots {α : Type z} {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : Slot (expand p f) → List α) :
    collect (expand p f) h = collect p (fun i =>
      collect (f i) (fun j => h ((slotExpand p f).symm ⟨i, j⟩))) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change collect ((expand p (fun i => f (.inl i))).comp (f (.inr ()))) h = _
    rw [collect_comp_slots, ih]
    rfl

/-- The canonical occurrence transport across an equality of endpoint-indexed paths. -/
def slotCast {a b : V} {p q : Quiver.Path a b} (h : p = q) : Slot p ≃ Slot q :=
  h ▸ Equiv.refl (Slot p)

@[simp] theorem slotCast_rfl {a b : V} (p : Quiver.Path a b) :
    slotCast (rfl : p = p) = Equiv.refl (Slot p) := rfl

@[simp] theorem componentAt_slotCast {a b : V} {p q : Quiver.Path a b}
    (h : p = q) (i : Slot p) : componentAt q (slotCast h i) = componentAt p i := by
  cases h; rfl

/-- Occurrence transport of a component-indexed family across path equality. -/
def pathFamilyCast (F : Component V → Sort z) {a b : V} {p q : Quiver.Path a b}
    (h : p = q) (f : ∀ i : Slot p, F (componentAt p i)) :
    ∀ i : Slot q, F (componentAt q i) := h ▸ f

@[simp] theorem pathFamilyCast_rfl (F : Component V → Sort z) {a b : V}
    {p : Quiver.Path a b} (f : ∀ i : Slot p, F (componentAt p i)) :
    pathFamilyCast F rfl f = f := rfl

/-- Transport commutes with adjoining a final edge, so all empty-prefix cases are covered. -/
@[simp] theorem slotCast_cons {a b c : V} {p q : Quiver.Path a b}
    (h : p = q) (e : b ⟶ c) (i : Slot p) :
    slotCast (congrArg (fun r => r.cons e) h) (.inl i) = .inl (slotCast h i) := by
  cases h; rfl

@[simp] theorem slotCast_cons_last {a b c : V} {p q : Quiver.Path a b}
    (h : p = q) (e : b ⟶ c) :
    slotCast (congrArg (fun r => r.cons e) h) (.inr ()) = .inr () := by
  cases h; rfl

@[simp] theorem slotCast_symm {a b : V} {p q : Quiver.Path a b} (h : p = q) :
    (slotCast h).symm = slotCast h.symm := by cases h; rfl

/-- The identity expansion's canonical occurrence map is the identity, not a permutation. -/
theorem slotExpand_edges_symm {a b : V} (p : Quiver.Path a b) (i : Slot p) :
    (slotExpand p (fun i => (componentAt p i).edge.toPath)).symm ⟨i, .inr ()⟩ =
      (slotCast (expand_edges p)).symm i := by
  induction p with
  | nil => exact nomatch i
  | cons p e ih =>
    cases i with
    | inl i =>
      change Sum.inl ((slotExpand p (fun i => (componentAt p i).edge.toPath)).symm
        ⟨i, .inr ()⟩) = _
      rw [ih]
      simp only [slotCast_symm]
      exact (slotCast_cons (expand_edges p).symm e i).symm
    | inr i =>
      cases i
      change Sum.inr () = _
      simp only [slotCast_symm]
      exact (slotCast_cons_last (expand_edges p).symm e).symm

/-- Triple concatenation has the canonical, occurrence-wise sum associator. -/
theorem slotComp_assoc {a b c d : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (r : Quiver.Path c d) (i : (Slot p ⊕ Slot q) ⊕ Slot r) :
    slotCast (Quiver.Path.comp_assoc p q r)
      ((slotComp (p.comp q) r).symm (Sum.map (slotComp p q).symm id i)) =
    (slotComp p (q.comp r)).symm
      (Sum.map id (slotComp q r).symm (Equiv.sumAssoc (Slot p) (Slot q) (Slot r) i)) := by
  induction r with
  | nil =>
    rcases i with (i | i) | i
    · rfl
    · rfl
    · exact nomatch i
  | cons r e ih =>
    rcases i with (i | i) | (i | ⟨⟩)
    · change slotCast (Quiver.Path.comp_assoc p q (r.cons e))
        (.inl ((slotComp (p.comp q) r).symm (.inl ((slotComp p q).symm (.inl i))))) = _
      rw [show Quiver.Path.comp_assoc p q (r.cons e) =
        congrArg (fun t => t.cons e) (Quiver.Path.comp_assoc p q r) from rfl]
      erw [slotCast_cons (Quiver.Path.comp_assoc p q r)]
      exact congrArg Sum.inl (ih (.inl (.inl i)))
    · change slotCast (Quiver.Path.comp_assoc p q (r.cons e))
        (.inl ((slotComp (p.comp q) r).symm (.inl ((slotComp p q).symm (.inr i))))) = _
      rw [show Quiver.Path.comp_assoc p q (r.cons e) =
        congrArg (fun t => t.cons e) (Quiver.Path.comp_assoc p q r) from rfl]
      erw [slotCast_cons (Quiver.Path.comp_assoc p q r)]
      exact congrArg Sum.inl (ih (.inl (.inr i)))
    · change slotCast (Quiver.Path.comp_assoc p q (r.cons e))
        (.inl ((slotComp (p.comp q) r).symm (.inr i))) = _
      rw [show Quiver.Path.comp_assoc p q (r.cons e) =
        congrArg (fun t => t.cons e) (Quiver.Path.comp_assoc p q r) from rfl]
      erw [slotCast_cons (Quiver.Path.comp_assoc p q r)]
      exact congrArg Sum.inl (ih (.inr i))
    · change slotCast (Quiver.Path.comp_assoc p q (r.cons e)) (.inr ()) = .inr ()
      exact slotCast_cons_last (Quiver.Path.comp_assoc p q r) e

/-- Component transport also transports occurrences of the same underlying path. -/
def componentPathSlotCast {c d : Component V} (h : c = d)
    (p : Quiver.Path c.source c.target) :
    Slot p ≃ Slot (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p) := by
  cases h
  exact Equiv.refl _

/-- Component transport leaves the order and multiplicity of occurrences unchanged. -/
theorem collect_componentPathSlotCast {α : Type z} {c d : Component V} (h : c = d)
    (p : Quiver.Path c.source c.target) (f : Slot p → List α) :
    collect p f = collect (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p)
      (fun j => f ((componentPathSlotCast h p).symm j)) := by
  cases h; rfl

/-- Equality transport leaves the order and multiplicity of occurrences unchanged. -/
theorem collect_slotCast {α : Type z} {a b : V} {p q : Quiver.Path a b} (h : p = q)
    (f : Slot p → List α) :
    collect p f = collect q (fun i => f ((slotCast h).symm i)) := by cases h; rfl

@[simp] theorem length_collect_singleton {α : Type z} {a b : V} (p : Quiver.Path a b)
    (f : Slot p → α) : (collect p (fun i => [f i])).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [collect, List.length_append, List.length_singleton,
      Quiver.Path.length_cons, ih]

/-- Ordered singleton collection detects the entire assignment, not merely its support. -/
theorem collect_singleton_injective {α : Type z} {a b : V} (p : Quiver.Path a b) :
    Function.Injective (fun f : Slot p → α => collect p (fun i => [f i])) := by
  intro f g h
  induction p with
  | nil => funext i; exact nomatch i
  | cons p e ih =>
    change collect p (fun i => [f (.inl i)]) ++ [f (.inr ())] =
      collect p (fun i => [g (.inl i)]) ++ [g (.inr ())] at h
    have hh := List.append_inj h (by simp only [length_collect_singleton])
    have h₁ := ih hh.1
    have h₂ : f (.inr ()) = g (.inr ()) := by simpa only [List.cons.injEq, and_true] using hh.2
    funext i
    cases i with
    | inl i => exact congrFun h₁ i
    | inr i => cases i; exact h₂

/-- Constructive fibrewise sigma equivalence, with explicit inverse proofs. -/
def occurrenceSigmaCongrRight {α : Type*} {β γ : α → Type*}
    (e : ∀ a, β a ≃ γ a) : (Σ a, β a) ≃ (Σ a, γ a) where
  toFun x := ⟨x.1, e x.1 x.2⟩
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv := by rintro ⟨a, b⟩; exact congrArg (Sigma.mk a) ((e a).symm_apply_apply b)
  right_inv := by rintro ⟨a, b⟩; exact congrArg (Sigma.mk a) ((e a).apply_symm_apply b)

/-- The twice-expanded occurrences, reassociated into three independently indexed stages. -/
def slotExpandAssocLeft {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target) :
    Slot (expand (expand p f) h) ≃
      (Σ i : Slot p, Σ j : Slot (f i),
        Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)) :=
  (slotExpand (expand p f) h).trans
    ((Equiv.sigmaCongrLeft' (slotExpand p f)).trans
      ((occurrenceSigmaCongrRight (fun ij => componentPathSlotCast
          (componentAt_slotExpand_symm p f ij) (h ((slotExpand p f).symm ij)))).trans
        (Equiv.sigmaAssoc (fun i j =>
          Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)))))

/-- The other bracketing has exactly the same three-stage occurrence indices. -/
def slotExpandAssocRight {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target) :
    Slot (expand p (fun i => expand (f i)
      (expandFamily (fun c => Quiver.Path c.source c.target) p f h i))) ≃
      (Σ i : Slot p, Σ j : Slot (f i),
        Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)) :=
  (slotExpand p _).trans (occurrenceSigmaCongrRight (fun i => slotExpand (f i) _))

@[simp] theorem slotExpandAssocLeft_symm_apply {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (i : Slot p) (j : Slot (f i))
    (k : Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)) :
    (slotExpandAssocLeft p f h).symm ⟨i, j, k⟩ =
      (slotExpand (expand p f) h).symm ⟨(slotExpand p f).symm ⟨i, j⟩,
        (componentPathSlotCast (componentAt_slotExpand_symm p f ⟨i, j⟩)
          (h ((slotExpand p f).symm ⟨i, j⟩))).symm k⟩ := rfl

@[simp] theorem slotExpandAssocRight_symm_apply {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (i : Slot p) (j : Slot (f i))
    (k : Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)) :
    (slotExpandAssocRight p f h).symm ⟨i, j, k⟩ =
      (slotExpand p _).symm ⟨i, (slotExpand (f i) _).symm ⟨j, k⟩⟩ := rfl

/-- The left-bracketed triple-slot equivalence preserves the full ordered collection. -/
theorem collect_slotExpandAssocLeft {α : Type z} {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (k : Slot (expand (expand p f) h) → List α) :
    collect (expand (expand p f) h) k =
      collect p (fun i => collect (f i) (fun j =>
        collect (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)
          (fun l => k ((slotExpandAssocLeft p f h).symm ⟨i, j, l⟩)))) := by
  rw [collect_expand_slots, collect_expand_slots]
  congr 1
  funext i
  congr 1
  funext j
  exact collect_componentPathSlotCast (componentAt_slotExpand_symm p f ⟨i, j⟩)
    (h ((slotExpand p f).symm ⟨i, j⟩)) _

/-- The right-bracketed triple-slot equivalence preserves the same ordered collection. -/
theorem collect_slotExpandAssocRight {α : Type z} {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (k : Slot (expand p (fun i => expand (f i)
      (expandFamily (fun c => Quiver.Path c.source c.target) p f h i))) → List α) :
    collect _ k =
      collect p (fun i => collect (f i) (fun j =>
        collect (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)
          (fun l => k ((slotExpandAssocRight p f h).symm ⟨i, j, l⟩)))) := by
  rw [collect_expand_slots]
  congr 1
  funext i
  exact collect_expand_slots (f i) _ _

/-- Full triple-occurrence coherence: expanding in either bracketing induces the same
three-stage occurrence, after the named canonical profile equality. -/
theorem slotExpand_assoc {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (i : Slot (expand (expand p f) h)) :
    slotExpandAssocRight p f h (slotCast (expand_assoc p f h) i) =
      slotExpandAssocLeft p f h i := by
  let eL := slotExpandAssocLeft p f h
  let eR := slotExpandAssocRight p f h
  let eC := slotCast (expand_assoc p f h)
  have hL := collect_slotExpandAssocLeft p f h (fun i => [eL i])
  have hR := collect_slotExpandAssocRight p f h (fun i => [eR i])
  simp only [eL, Equiv.apply_symm_apply] at hL
  simp only [eR, Equiv.apply_symm_apply] at hR
  have hC := collect_slotCast (expand_assoc p f h) (fun i => [eL i])
  have hh : (fun j => eL (eC.symm j)) = (fun j => eR j) :=
    collect_singleton_injective _ (hC.symm.trans (hL.trans hR.symm))
  have hi := congrFun hh (eC i)
  simpa only [Equiv.symm_apply_apply] using hi.symm

/-- The inverse form exposes the exact canonical correspondence for substitution laws. -/
theorem slotExpand_assoc_symm {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (i : Slot p) (j : Slot (f i))
    (k : Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)) :
    slotCast (expand_assoc p f h) ((slotExpandAssocLeft p f h).symm ⟨i, j, k⟩) =
      (slotExpandAssocRight p f h).symm ⟨i, j, k⟩ := by
  apply (slotExpandAssocRight p f h).injective
  rw [slotExpand_assoc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp] theorem componentAt_slotCast_symm {a b : V} {p q : Quiver.Path a b}
    (h : p = q) (i : Slot q) :
    componentAt p ((slotCast h).symm i) = componentAt q i := by cases h; rfl

/-- The family cast is explicitly the inverse occurrence map followed by component transport. -/
theorem pathFamilyCast_apply (F : Component V → Sort z) {a b : V}
    {p q : Quiver.Path a b} (h : p = q)
    (f : ∀ i : Slot p, F (componentAt p i)) (i : Slot q) :
    pathFamilyCast F h f i = occurrenceTransport F (componentAt_slotCast_symm h i)
      (f ((slotCast h).symm i)) := by cases h; rfl

@[simp] theorem componentAt_componentPathSlotCast_symm {c d : Component V}
    (h : c = d) (p : Quiver.Path c.source c.target)
    (i : Slot (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p)) :
    componentAt p ((componentPathSlotCast h p).symm i) =
      componentAt (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p) i := by
  cases h; rfl

/-- A family can be transported along a change of the containing component. -/
def componentPathFamilyCast (F : Component V → Sort z) {c d : Component V}
    (h : c = d) (p : Quiver.Path c.source c.target)
    (f : ∀ i : Slot p, F (componentAt p i)) :
    ∀ i : Slot (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p),
      F (componentAt (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p) i) := by
  cases h; exact f

/-- Component-family transport uses the explicit inverse occurrence map. -/
theorem componentPathFamilyCast_apply (F : Component V → Sort z) {c d : Component V}
    (h : c = d) (p : Quiver.Path c.source c.target)
    (f : ∀ i : Slot p, F (componentAt p i))
    (i : Slot (occurrenceTransport (fun c => Quiver.Path c.source c.target) h p)) :
    componentPathFamilyCast F h p f i =
      occurrenceTransport F (componentAt_componentPathSlotCast_symm h p i)
        (f ((componentPathSlotCast h p).symm i)) := by cases h; rfl

/-- Equality of occurrences, not equality of their labels, suffices to compare reindexed values. -/
theorem occurrenceTransport_family_congr (F : Component V → Sort z) {α : Type*}
    (c : α → Component V) (f : ∀ i, F (c i)) {i j : α} (h : i = j)
    {d : Component V} (hi : c i = d) (hj : c j = d) :
    occurrenceTransport F hi (f i) = occurrenceTransport F hj (f j) := by
  cases h; rfl

/-- Naturality of dependent occurrence families under the triple expansion associator.
This is the component-typed family form of `slotExpand_assoc`, suitable for fibre substitution. -/
theorem expandFamily_assoc (F : Component V → Sort z) {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f),
      Quiver.Path (componentAt (expand p f) i).source (componentAt (expand p f) i).target)
    (k : ∀ i : Slot (expand (expand p f) h), F (componentAt (expand (expand p f) h) i))
    (i : Slot p) (j : Slot (f i))
    (l : Slot (expandFamily (fun c => Quiver.Path c.source c.target) p f h i j)) :
    expandFamily F (f i)
      (expandFamily (fun c => Quiver.Path c.source c.target) p f h i)
      (expandFamily F p
        (fun i => expand (f i) (expandFamily (fun c => Quiver.Path c.source c.target) p f h i))
        (pathFamilyCast F (expand_assoc p f h) k) i) j l =
    componentPathFamilyCast F (componentAt_slotExpand_symm p f ⟨i, j⟩)
      (h ((slotExpand p f).symm ⟨i, j⟩))
      (expandFamily F (expand p f) h k ((slotExpand p f).symm ⟨i, j⟩)) l := by
  rw [componentPathFamilyCast_apply]
  unfold expandFamily
  rw [pathFamilyCast_apply]
  simp only [occurrenceTransport_trans]
  apply occurrenceTransport_family_congr F (componentAt (expand (expand p f) h)) k
  have hh := congrArg (fun x => (slotCast (expand_assoc p f h)).symm x)
    (slotExpand_assoc_symm p f h i j l)
  simp only [Equiv.symm_apply_apply, slotExpandAssocLeft_symm_apply,
    slotExpandAssocRight_symm_apply] at hh
  unfold expandFamily at hh
  exact hh.symm

/-- Component transport commutes with every component-indexed map, including frontier. -/
theorem occurrenceTransport_natural (F : Component V → Sort z) (G : Component V → Sort z')
    (map : ∀ c, F c → G c) {c d : Component V} (h : c = d) (x : F c) :
    map d (occurrenceTransport F h x) = occurrenceTransport G h (map c x) := by
  cases h; rfl

/-- Every component-indexed map commutes with canonical expansion-family reindexing. -/
theorem expandFamily_natural (F : Component V → Sort z) (G : Component V → Sort z')
    (map : ∀ c, F c → G c) {a b : V} (p : Quiver.Path a b)
    (f : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (h : ∀ i : Slot (expand p f), F (componentAt (expand p f) i))
    (i : Slot p) (j : Slot (f i)) :
    map (componentAt (f i) j) (expandFamily F p f h i j) =
      expandFamily G p f (fun i => map _ (h i)) i j :=
  occurrenceTransport_natural F G map _ _

/-- Right-unit coherence for arbitrary component-indexed families. -/
theorem expandFamily_edges (F : Component V → Sort z) {a b : V} (p : Quiver.Path a b)
    (h : ∀ i : Slot (expand p (fun i => (componentAt p i).edge.toPath)),
      F (componentAt (expand p (fun i => (componentAt p i).edge.toPath)) i))
    (i : Slot p) :
    expandFamily F p (fun i => (componentAt p i).edge.toPath) h i (.inr ()) =
      pathFamilyCast F (expand_edges p) h i := by
  rw [pathFamilyCast_apply]
  unfold expandFamily
  exact occurrenceTransport_family_congr F _ h (slotExpand_edges_symm p i) _ _

/-- Empty-prefix coherence for concatenation occurrences. -/
theorem slotComp_nil_left {a b : V} (p : Quiver.Path a b) (i : Slot p) :
    slotCast (Quiver.Path.nil_comp p) ((slotComp .nil p).symm (.inr i)) = i := by
  induction p with
  | nil => exact nomatch i
  | cons p e ih =>
    cases i with
    | inl i =>
      change slotCast (Quiver.Path.nil_comp (p.cons e))
        (.inl ((slotComp .nil p).symm (.inr i))) = .inl i
      erw [slotCast_cons (Quiver.Path.nil_comp p)]
      exact congrArg Sum.inl (ih i)
    | inr i =>
      cases i
      exact slotCast_cons_last (Quiver.Path.nil_comp p) e

/-- Expanding the identity profile returns its sole replacement, including an empty replacement. -/
theorem expand_edge (c : Component V)
    (f : ∀ i : Slot c.edge.toPath,
      Quiver.Path (componentAt c.edge.toPath i).source (componentAt c.edge.toPath i).target) :
    expand c.edge.toPath f = f (.inr ()) := Quiver.Path.nil_comp _

/-- Left-unit coherence is an equality of occurrences, including empty replacement paths. -/
theorem slotExpand_edge_symm (c : Component V)
    (f : ∀ i : Slot c.edge.toPath,
      Quiver.Path (componentAt c.edge.toPath i).source (componentAt c.edge.toPath i).target)
    (i : Slot (f (.inr ()))) :
    (slotExpand c.edge.toPath f).symm ⟨.inr (), i⟩ =
      (slotCast (expand_edge c f)).symm i := by
  apply (slotCast (expand_edge c f)).injective
  rw [Equiv.apply_symm_apply]
  exact slotComp_nil_left _ i

/-- Left-unit coherence for arbitrary component-indexed families. -/
theorem expandFamily_edge (F : Component V → Sort z) (c : Component V)
    (f : ∀ i : Slot c.edge.toPath,
      Quiver.Path (componentAt c.edge.toPath i).source (componentAt c.edge.toPath i).target)
    (h : ∀ i : Slot (expand c.edge.toPath f), F (componentAt (expand c.edge.toPath f) i))
    (i : Slot (f (.inr ()))) :
    expandFamily F c.edge.toPath f h (.inr ()) i =
      pathFamilyCast F (expand_edge c f) h i := by
  rw [pathFamilyCast_apply]
  unfold expandFamily
  exact occurrenceTransport_family_congr F _ h (slotExpand_edge_symm c f i) _ _

end WitnessedDecompositions.Path








