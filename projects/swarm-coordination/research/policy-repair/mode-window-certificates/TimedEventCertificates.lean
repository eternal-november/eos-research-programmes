import Mathlib

namespace SwarmTimedEvents

structure Arc (V : Type) where
  src : V
  dst : V
  bound : ℤ

def Respects {V : Type} (clock : V → ℤ) (e : Arc V) : Prop :=
  clock e.dst - clock e.src ≤ e.bound

inductive Chain {V : Type} : V → List (Arc V) → V → Prop where
  | nil (u : V) : Chain u [] u
  | cons (e : Arc V) {tail : List (Arc V)} {w : V}
      (p : Chain e.dst tail w) : Chain e.src (e :: tail) w

theorem path_bound {V : Type} (clock : V → ℤ) {u v : V} {es : List (Arc V)}
    (p : Chain u es v) (h : ∀ e ∈ es, Respects clock e) :
    clock v - clock u ≤ (es.map Arc.bound).sum := by
  induction p with
  | nil u => simp
  | @cons e tail w p ih =>
    have h₁ : clock e.dst - clock e.src ≤ e.bound :=
      h e (List.mem_cons_self ..)
    have h₂ : clock w - clock e.dst ≤ (tail.map Arc.bound).sum :=
      ih (fun a ha => h a (List.mem_cons_of_mem e ha))
    simp only [List.map_cons,List.sum_cons]
    linarith

theorem negative_cycle_obstructs {V : Type} {u : V} {es : List (Arc V)}
    (p : Chain u es u) (neg : (es.map Arc.bound).sum < 0) :
    ¬ ∃ clock : V → ℤ, ∀ e ∈ es, Respects clock e := by
  rintro ⟨clock,hclock⟩
  have h := path_bound clock p hclock
  linarith

theorem old_cycle_still_refutes {V : Type} {u : V} {es : List (Arc V)}
    (p : Chain u es u) (neg : (es.map Arc.bound).sum < 0)
    (new : Set (Arc V))
    (preserved : ∀ e ∈ es, ∃ e' ∈ new, e'.src = e.src ∧ e'.dst = e.dst ∧ e'.bound ≤ e.bound) :
    ¬ ∃ clock : V → ℤ, ∀ e ∈ new, Respects clock e := by
  rintro ⟨clock,h⟩
  apply negative_cycle_obstructs p neg
  refine ⟨clock,fun e he => ?_⟩
  obtain ⟨e',he',hs,hd,hb⟩ := preserved e he
  have h' : clock e'.dst - clock e'.src ≤ e'.bound := h e' he'
  rw [hs,hd] at h'
  exact h'.trans hb

#print axioms path_bound
#print axioms negative_cycle_obstructs
#print axioms old_cycle_still_refutes
end SwarmTimedEvents
