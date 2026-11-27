import Mathlib

namespace ReceiptErasure

def Causal (Obs Act : Type) := List Obs → Act

def decorate {Obs : Type} (visible ownCommit : Obs → Bool)
    (oldPaid : Bool) (v : Obs) : Obs × Option Bool :=
  (v, if visible v then some (oldPaid || ownCommit v) else none)

def specialize {Obs Act : Type} (visible ownCommit : Obs → Bool)
    (oldPaid : Bool) (active : Causal (Obs × Option Bool) Act) :
    Causal Obs Act :=
  fun hist => active (hist.map (decorate visible ownCommit oldPaid))

def trace {Obs Act Plant : Type} (emit : Plant → List (Obs × Act) → Act → Obs)
    (p : Causal Obs Act) (z : Plant) :
    Nat → List (Obs × Act)
  | 0 => []
  | n+1 =>
    let h := trace emit p z n
    let a := p (h.map Prod.fst)
    h ++ [(emit z h a, a)]

@[simp] theorem no_read_forgery {Obs : Type} (visible ownCommit : Obs → Bool)
    (b : Bool) (v : Obs) (h : visible v = false) :
    (decorate visible ownCommit b v).2 = none := by
  simp [decorate, h]

theorem finite_trace_erasure {Obs Act Plant : Type}
    (emit : Plant → List (Obs × Act) → Act → Obs)
    (visible ownCommit : Obs → Bool)
    (p : Causal (Obs × Option Bool) Act)
    (allowed : Plant → Bool → Prop)
    (service : Plant → List (Obs × Act) → Bool → Prop)
    (horizon : Nat)
    (shadow : ∀ z, allowed z true → allowed z false)
    (mono : ∀ z hist, service z hist false → service z hist true)
    (ok : ∀ z b, allowed z b →
       service z (trace emit (specialize visible ownCommit b p) z horizon) b) :
    ∃ q : Causal Obs Act,
      ∀ z b, allowed z b → service z (trace emit q z horizon) b := by
  refine ⟨specialize visible ownCommit false p, ?_⟩
  intro z b law
  cases b with
  | false => exact ok z false law
  | true => exact mono z _ (ok z false (shadow z law))

-- A contingent earlier exit is a real violation of monotonicity:
-- the same trace meeting the ordinary late deadline need not meet
-- the earlier paid-history service promise.
theorem early_deadline_breaks_mono (late early tick : Nat)
    (h₁ : tick ≤ late) (h₂ : early < tick) :
    ¬ ((tick ≤ late) → (tick ≤ early)) := by omega

#print axioms finite_trace_erasure
#print axioms no_read_forgery
#print axioms early_deadline_breaks_mono
end ReceiptErasure
