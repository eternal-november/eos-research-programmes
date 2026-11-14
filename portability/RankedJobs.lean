import Std

/-! Mechanized helpers for the finite ranked-job interface.
These prove represented-path and rule-footprint laws, not source realizability,
physical time divergence, initialized recurrent recovery, or RP0-RP6 completion.
Rational edge budgets can be scaled by one common finite denominator; no local
clock synchronization or runtime knowledge of that analytic unit is inferred. -/
namespace PortabilityJobs

inductive Path {S : Type} (Step : S → Nat → S → Prop) : S → Nat → Nat → S → Prop where
  | nil (s : S) : Path Step s 0 0 s
  | cons {s u v : S} {cost total length : Nat} :
      Step s cost u → Path Step u total length v →
      Path Step s (cost + total) (length + 1) v

 theorem elapsed_bound {S : Type} (Step : S → Nat → S → Prop)
    (remaining : S → Nat)
    (edge : ∀ s cost u, Step s cost u → cost + remaining u ≤ remaining s)
    {s u : S} {cost length : Nat} (path : Path Step s cost length u) :
    cost + remaining u ≤ remaining s := by
  induction path with
  | nil s => simp
  | cons step tail ih =>
    have h := edge _ _ _ step
    omega

 theorem length_bound {S : Type} (Step : S → Nat → S → Prop)
    (rank : S → Nat)
    (decreases : ∀ s cost u, Step s cost u → rank u < rank s)
    {s u : S} {cost length : Nat} (path : Path Step s cost length u) :
    length + rank u ≤ rank s := by
  induction path with
  | nil s => simp
  | cons step tail ih =>
    have h := decreases _ _ _ step
    omega

 theorem terminal_reachable {S : Type} (Step : S → Nat → S → Prop)
    (rank : S → Nat) (terminal : S → Prop)
    (decreases : ∀ s cost u, Step s cost u → rank u < rank s)
    (total : ∀ s, terminal s ∨ ∃ cost u, Step s cost u) :
    ∀ s, ∃ cost length u, Path Step s cost length u ∧ terminal u := by
  intro s
  generalize hx : rank s = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    rcases total s with done | ⟨cost,u,step⟩
    · exact ⟨0,0,s,Path.nil s,done⟩
    · have less : rank u < n := by have h := decreases s cost u step; omega
      obtain ⟨rest,len,v,path,done⟩ := ih (rank u) less u rfl
      exact ⟨cost+rest,len+1,v,Path.cons step path,done⟩

 theorem no_unbounded_rank_descent (rank : Nat → Nat)
    (decreases : ∀ k, rank (k+1) < rank k) : False := by
  have bounded : ∀ k, k + rank k ≤ rank 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => have h := decreases k; omega
  have h := bounded (rank 0+1)
  omega

 theorem local_rules_assemble {Index State : Type}
    (holds : Index → State → Prop) (affected reads : Index → Prop)
    (before after : State)
    (allBefore : ∀ i, holds i before)
    (changed : ∀ i, affected i → (∀ j, reads j → holds j before) → holds i after)
    (frame : ∀ i, ¬ affected i → holds i before → holds i after) :
    ∀ i, holds i after := by
  intro i
  by_cases touch : affected i
  · exact changed i touch (fun j _ => allBefore j)
  · exact frame i touch (allBefore i)

 theorem strict_prefix_end (release commissioning bound horizon : Nat)
    (slack : commissioning + bound < horizon) :
    max release commissioning + bound < release + horizon := by
  omega

#print axioms elapsed_bound
#print axioms length_bound
#print axioms terminal_reachable
#print axioms no_unbounded_rank_descent
#print axioms local_rules_assemble
#print axioms strict_prefix_end

end PortabilityJobs
