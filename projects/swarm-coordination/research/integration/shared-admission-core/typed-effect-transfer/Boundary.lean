import Mathlib

namespace EffectBoundary

/-- Completeness relative to declared possible writers. An implementation
guard is sufficient exactly when every legal prefix event is covered. -/
theorem coversAllPossible {W : Type} (reachable covered : W → Prop) :
    (∀ run : List W, (∀ w ∈ run, reachable w) → ∀ w ∈ run, covered w) ↔
    (∀ w, reachable w → covered w) := by
  constructor
  · intro h w r
    apply h [w] _ w (by simp)
    intro x hx
    have same : x = w := by simpa using hx
    simpa [same] using r
  · intro h run legal w hw
    exact h w (legal w hw)

theorem writerExtensionNeedsNewProof {W : Type} (covered old new : W → Prop)
    (oldOK : ∀ w, old w → covered w) :
    (∀ w, old w ∨ new w → covered w) ↔ (∀ w, new w → covered w) := by
  constructor
  · intro h w hn
    exact h w (Or.inr hn)
  · intro h w hn
    exact hn.elim (oldOK w) (h w)

theorem terminalTruthNeedsAfterFence (read fence actuation : Nat)
    (pending : read < actuation) (closed : actuation ≤ fence) :
    read < fence := by omega

end EffectBoundary

#print axioms EffectBoundary.coversAllPossible
#print axioms EffectBoundary.writerExtensionNeedsNewProof
#print axioms EffectBoundary.terminalTruthNeedsAfterFence
