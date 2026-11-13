module

public import WitnessedDecompositions.Congruence

/-! Additive primitive-witness statistics provide nontrivial parallel congruences. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace WitnessedDecompositions
namespace Path
variable {V : Type u} [Quiver.{v} V]

/-- Sum a natural-valued statistic independently over every profile position. -/
def sum {a b : V} (p : Quiver.Path a b) (f : Slot p → Nat) : Nat :=
  (collect p (fun i => [f i])).sum

@[simp] theorem sum_nil {a : V} (f : Slot (Quiver.Path.nil (a := a)) → Nat) : sum .nil f = 0 := rfl

@[simp] theorem sum_cons {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (f : Slot (p.cons e) → Nat) : sum (p.cons e) f = sum p (fun i => f (.inl i)) + f (.inr ()) := by
  simp [sum, collect]

theorem sum_add {a b : V} (p : Quiver.Path a b) (f g : Slot p → Nat) :
    sum p (fun i => f i + g i) = sum p f + sum p g := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [sum_cons, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sum_collect {a b : V} (p : Quiver.Path a b) (f : Slot p → List Nat) :
    (collect p f).sum = sum p (fun i => (f i).sum) := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [collect, sum_cons, ih]

theorem sum_expand {a b : V} (p : Quiver.Path a b)
    (q : ∀ i : Slot p, Quiver.Path (componentAt p i).source (componentAt p i).target)
    (f : Slot (expand p q) → Nat) :
    sum (expand p q) f = sum p (fun i => sum (q i)
      (fun j => f ((slotExpand p q).symm ⟨i, j⟩))) := by
  unfold sum
  rw [collect_expand_slots, sum_collect]
  rfl

end Path
namespace Tree
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Every primitive keeps its independently declared natural-valued weight. -/
def weight (w : S.Generator → Nat) : {c : Component V} → Tree S c → Nat
  | _, .leaf _ => 0
  | _, .node g children => w g + Path.sum (S.input g) (fun i => weight w (children i))

@[simp] theorem weight_transport (w : S.Generator → Nat) {c d : Component V}
    (h : c = d) (t : Tree S c) : weight w (Path.occurrenceTransport (Tree S) h t) = weight w t := by
  cases h
  rfl

/-- The statistic is additive under actual occurrence-wise substitution. -/
theorem weight_profileGraft (w : S.Generator → Nat) {c : Component V} (t : Tree S c)
    (f : (collection S).Family (frontier t)) :
    weight w (profileGraft t f) = weight w t + Path.sum (frontier t) (fun i => weight w (f i)) := by
  induction t with
  | leaf c =>
    change weight w (f (.inr ())) = 0 + ([weight w (f (.inr ()))].sum)
    simp
  | node g children ih =>
    change w g + Path.sum (S.input g) (fun i => weight w
      (profileGraft (children i)
        (Path.expandFamily (Tree S) (S.input g) (fun i => frontier (children i)) f i))) = _
    simp only [ih]
    rw [Path.sum_add]
    change w g + (Path.sum (S.input g) (fun i => weight w (children i)) + _) =
      (w g + Path.sum (S.input g) (fun i => weight w (children i))) + _
    rw [Nat.add_assoc]
    congr 1
    congr 1
    apply Eq.trans ?_ (Path.sum_expand (S.input g)
      (fun i => frontier (children i)) (fun i => weight w (f i))).symm
    congr 1
    funext i
    congr 1
    funext j
    exact weight_transport w _ _

theorem sum_weight_reindex (w : S.Generator → Nat) {a b : V}
    {p q : Quiver.Path a b} (h : p = q) (f : (collection S).Family q) :
    Path.sum p (fun i => weight w ((collection S).reindex h f i)) =
      Path.sum q (fun i => weight w (f i)) := by
  cases h
  rfl

/-- Additivity is stated at independently prescribed operation fibres as well. -/
theorem weight_substituteOperation (w : S.Generator → Nat)
    {c : Component V} {p : Quiver.Path c.source c.target}
    (t : Operation (S := S) c p)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (f : ∀ i : Path.Slot p, Operation (S := S) (Path.componentAt p i) (q i)) :
    weight w (substituteOperation t q f).val =
      weight w t.val + Path.sum p (fun i => weight w (f i).val) := by
  change weight w (profileGraft t.val ((collection S).reindex t.property (fun i => (f i).val))) = _
  rw [weight_profileGraft, sum_weight_reindex]

/-- Equal ordered profiles and equal primitive statistics form a parallel congruence. -/
def weightCongruence (w : S.Generator → Nat) : ParallelCongruence (freeCalc S) where
  Rel a b := frontier a = frontier b ∧ weight w a = weight w b
  refl _ := ⟨rfl, rfl⟩
  symm h := ⟨h.1.symm, h.2.symm⟩
  trans h k := ⟨h.1.trans k.1, h.2.trans k.2⟩
  parallel h := h.1
  substitute a b hab q f g hfg := by
    refine ⟨(substituteOperation a q f).property.trans (substituteOperation b q g).property.symm, ?_⟩
    change weight w (substituteOperation a q f).val = weight w (substituteOperation b q g).val
    rw [weight_substituteOperation, weight_substituteOperation, hab.2]
    congr 1
    exact congrArg (Path.sum _) (funext (fun i => (hfg i).2))

end Tree
namespace Presentation
variable {V : Type u} [Quiver.{v} V] {S : Signature.{u, v, w} V}

/-- Any additive primitive statistic preserved by the declarations is preserved by derivability. -/
theorem derives_weight (E : Equations S) (w : S.Generator → Nat)
    (hE : ∀ c p (a b : Tree.Operation (S := S) c p), E c p a b →
      Tree.weight w a.val = Tree.weight w b.val)
    {c : Component V} {a b : Tree S c} (h : Derives S E a b) :
    Tree.weight w a = Tree.weight w b := by
  exact (derives_least E (Tree.weightCongruence w)
    (fun c p a b he => ⟨a.property.trans b.property.symm, hE c p a b he⟩) h).2

end Presentation
end WitnessedDecompositions
