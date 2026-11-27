import Lean
namespace CutTransport
def Ideal {E : Type} (r : E → E → Prop) (c : E → Prop) : Prop :=
  ∀ x y, r x y → c y → c x
def Requires {E : Type} (p c : E → Prop) : Prop := ∀ x, p x → c x
def Close {E : Type} (r : E → E → Prop) (p : E → Prop) (x : E) :=
  ∃ y, p y ∧ r x y

theorem requires_close_iff {E : Type} (r : E → E → Prop)
    (refl : ∀ x, r x x) (p c : E → Prop) (hc : Ideal r c) :
    Requires p c ↔ Requires (Close r p) c := by
  constructor
  · intro hp x hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact hc x y hxy (hp y hy)
  · intro hp x hx
    exact hp x ⟨x, hx, refl x⟩

theorem weaker_order_separates {E : Type} (r s : E → E → Prop)
    (reflR : ∀ x, r x x) (reflS : ∀ x, s x x)
    (transS : ∀ x y z, s x y → s y z → s x z)
    (a b : E) (ab : r a b) (notAB : ¬ s a b) :
    ∃ p q c : E → Prop,
      (∀ d, Ideal r d → (Requires p d ↔ Requires q d)) ∧
      Ideal s c ∧ Requires p c ∧ ¬ Requires q c := by
  let c : E → Prop := fun x => s x b
  refine ⟨c, Close r c, c, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact requires_close_iff r reflR c d hd
  · intro x y hxy hy
    exact transS x y b hxy hy
  · intro x hx
    exact hx
  · intro h
    exact notAB (h a ⟨b, reflS b, ab⟩)

theorem preserved_order_transports {E : Type} (r s : E → E → Prop)
    (inc : ∀ a b, r a b → s a b)
    (p q : (E → Prop) → Prop)
    (agree : ∀ c, Ideal r c → (p c ↔ q c)) :
    ∀ c, Ideal s c → (p c ↔ q c) := by
  intro c hs
  exact agree c (fun x y hxy hy => hs x y (inc x y hxy) hy)

#print axioms requires_close_iff
#print axioms weaker_order_separates
#print axioms preserved_order_transports
end CutTransport
