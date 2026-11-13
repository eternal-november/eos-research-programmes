module

public import WitnessedDecompositions.PathOccurrences

@[expose] public section
universe u v w z z'
namespace WitnessedDecompositions.RelationalWitness
variable {V : Type u} [Quiver.{v} V]

/-- Constructive finite dependent choice for the actual ordered path slots.
The conclusion is in Prop; no data is extracted from Prop by classical choice. -/
theorem exists_slot_family {a b : V} (p : Quiver.Path a b)
    (Y : Path.Slot p → Type w) (P : ∀ i, Y i → Prop)
    (h : ∀ i, ∃ y, P i y) : ∃ f : ∀ i, Y i, ∀ i, P i (f i) := by
  induction p with
  | nil =>
    exact ⟨(fun i => nomatch i), fun i => nomatch i⟩
  | cons p e ih =>
    obtain ⟨f, hf⟩ := ih (fun i => Y (.inl i)) (fun i y => P (.inl i) y)
      (fun i => h (.inl i))
    obtain ⟨last, hlast⟩ := h (.inr ())
    refine ⟨(fun i => match i with | .inl j => f j | .inr () => last), ?_⟩
    rintro (i | ⟨⟩)
    · exact hf i
    · exact hlast

/-- The exact finite assembly equivalence used by relational associativity. -/
theorem forall_exists_iff {a b : V} (p : Quiver.Path a b)
    (Y : Path.Slot p → Type w) (P : ∀ i, Y i → Prop) :
    (∀ i, ∃ y, P i y) ↔ ∃ f : ∀ i, Y i, ∀ i, P i (f i) := by
  constructor
  · exact exists_slot_family p Y P
  · rintro ⟨f, hf⟩ i
    exact ⟨f i, hf i⟩

/-- Logical associativity of relations after the canonical slot-expansion
bijections have identified the two input tuples. All carriers are arbitrary. -/
theorem associative_witnesses {a b : V} (p : Quiver.Path a b)
    (A : Path.Slot p → Type w) (B : Path.Slot p → Type z)
    (Z : Type z') (R : (∀ i, A i) → Z → Prop)
    (S : ∀ i, B i → A i → Prop) (T : ∀ i, B i → Prop) (out : Z) :
    (∃ bs : ∀ i, B i,
      (∃ xs : ∀ i, A i, R xs out ∧ ∀ i, S i (bs i) (xs i)) ∧ ∀ i, T i (bs i)) ↔
    (∃ xs : ∀ i, A i, R xs out ∧ ∀ i, ∃ bs : B i, S i bs (xs i) ∧ T i bs) := by
  constructor
  · rintro ⟨bs, ⟨xs, hr, hs⟩, ht⟩
    exact ⟨xs, hr, fun i => ⟨bs i, hs i, ht i⟩⟩
  · rintro ⟨xs, hr, h⟩
    obtain ⟨bs, hb⟩ := exists_slot_family p B
      (fun i bs => S i bs (xs i) ∧ T i bs) h
    exact ⟨bs, ⟨xs, hr, fun i => (hb i).1⟩, fun i => (hb i).2⟩

/-- Right unit in product coordinates, including an empty dependent product. -/
theorem right_unit_witnesses {A : Type u} (X : A → Type v) (Z : Type w)
    (R : (∀ i, X i) → Z → Prop) (input : ∀ i, X i) (out : Z) :
    (∃ mid : ∀ i, X i, R mid out ∧ ∀ i, input i = mid i) ↔ R input out := by
  constructor
  · rintro ⟨mid, hr, hm⟩
    have h : input = mid := funext hm
    exact h ▸ hr
  · intro hr
    exact ⟨input, hr, fun _ => rfl⟩

/-- Left unit in singleton coordinates with arbitrary, possibly empty, carrier. -/
theorem left_unit_witnesses {A : Type u} (R : A → Prop) (out : A) :
    (∃ mid : A, mid = out ∧ R mid) ↔ R out := by
  constructor
  · rintro ⟨mid, rfl, hr⟩
    exact hr
  · intro hr
    exact ⟨out, rfl, hr⟩

#print axioms exists_slot_family
#print axioms forall_exists_iff
#print axioms associative_witnesses
#print axioms right_unit_witnesses
#print axioms left_unit_witnesses
end WitnessedDecompositions.RelationalWitness
