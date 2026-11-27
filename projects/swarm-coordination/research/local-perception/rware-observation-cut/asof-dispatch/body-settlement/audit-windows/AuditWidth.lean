import Mathlib

theorem exactNamedQueryLower {n k : ℕ}
    (encode : (Fin n → Bool) → Fin k)
    (decode : Fin k → Fin n → Bool)
    (sound : ∀ row i, decode (encode row) i = row i) :
    2 ^ n ≤ k := by
  have he : Function.Injective encode := by
    intro a b h
    funext i
    rw [← sound a i, ← sound b i, h]
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective encode he

theorem restrictedReadSurjective {n q : ℕ} (sites : Fin q ↪ Fin n) :
    Function.Surjective (fun row : Fin n → Bool => fun i => row (sites i)) := by
  classical
  intro word
  refine ⟨fun j => if h : ∃ i, sites i = j then word (Classical.choose h) else false, ?_⟩
  funext i
  have h : ∃ j, sites j = sites i := ⟨i, rfl⟩
  change (if H : ∃ j, sites j = sites i then word (Classical.choose H) else false) = word i
  rw [dite_eq_left h]
  exact congrArg word (sites.injective (Classical.choose_spec h))

theorem indexedAuditLower {n q k : ℕ} (selection : Fin q ↪ Fin n)
    (encode : (Fin n → Bool) → Fin k) (decode : Fin k → Fin q → Bool)
    (sound : ∀ row i, decode (encode row) i = row (selection i)) :
    2 ^ q ≤ k := by
  have hdec : Function.Surjective decode := by
    intro word
    obtain ⟨row, hp⟩ := restrictedReadSurjective selection word
    refine ⟨encode row, ?_⟩
    funext i
    exact (sound row i).trans (congrFun hp i)
  simpa [Fintype.card_fun] using Fintype.card_le_of_surjective decode hdec

#print axioms exactNamedQueryLower
#print axioms restrictedReadSurjective
#print axioms indexedAuditLower
