import Lean

namespace ExactScope

universe u v w x
variable {A : Type u} {B : Type v} {Key : Type w} {Effect : Type x}

def Image (read : A → Key) (run : A → Effect)
    (keep : Key → Prop) (k : Key) (e : Effect) : Prop :=
  keep k ∧ ∃ h, read h = k ∧ run h = e

def Service (read : A → Key) (run : A → Effect)
    (keep : Key → Prop) (require : Key → Effect → Prop) : Prop :=
  ∀ h, keep (read h) → require (read h) (run h)

theorem from_image (read : A → Key) (run : A → Effect)
    (keep : Key → Prop) (require : Key → Effect → Prop) :
    Service read run keep require ↔ ∀ k e, Image read run keep k e → require k e := by
  constructor
  · intro h k e r
    obtain ⟨g,t,hk,he⟩ := r
    subst k
    subst e
    exact h t g
  · intro h t g
    exact h _ _ ⟨g,t,rfl,rfl⟩

/-- Safety/service properties universal over the selected scope transport in the
direction from larger support to smaller support. The reverse requires more. -/
theorem transfer (rA : A → Key) (rB : B → Key) (a : A → Effect) (b : B → Effect)
    (s : Key → Prop) (law : Key → Effect → Prop)
    (newLifts : ∀ k e, Image rB b s k e → Image rA a s k e)
    (old : Service rA a s law) : Service rB b s law := by
  apply (from_image rB b s law).mpr
  intro k e z
  exact (from_image rA a s law).mp old k e (newLifts k e z)

/-- An old impossibility witness does not go in the same direction: witness
lifting needs the reverse inclusion on the particular selected fact. -/
theorem witness_transport (rA : A → Key) (rB : B → Key) (a : A → Effect) (b : B → Effect)
    (s : Key → Prop) (k : Key) (e : Effect)
    (oldLifts : Image rA a s k e → Image rB b s k e)
    (w : Image rA a s k e) : ∃ h, rB h = k ∧ b h = e :=
  (oldLifts w).2

#print axioms from_image
#print axioms transfer
#print axioms witness_transport
end ExactScope
