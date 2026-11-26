import Mathlib

inductive Recipe where
  | const : ℕ → Recipe
  | read : String → Recipe
  | cond : Recipe → Recipe → Recipe → Recipe

def run (s : String → ℕ) : Recipe → ℕ × Finset String
  | .const n => (n, {})
  | .read k => (s k, {k})
  | .cond c u v =>
    let test := run s c
    let body := if test.1 = 0 then run s v else run s u
    (body.1, test.2 ∪ body.2)

theorem traceStable (s t : String → ℕ) (r : Recipe)
    (agree : ∀ k ∈ (run s r).2, s k = t k) : run s r = run t r := by
  induction r with
  | const n => rfl
  | read k =>
    have h := agree k (by simp [run])
    simp [run,h]
  | cond c u v ihc ihu ihv =>
    by_cases hc : (run s c).1 = 0
    · have hread := agree
      simp [run,hc] at hread
      have tc : run s c = run t c := ihc (fun k hk => hread k (Or.inl hk))
      have tv : run s v = run t v := ihv (fun k hk => hread k (Or.inr hk))
      simp only [run]
      rw [←tc,←tv]
      simp [hc]
    · have hread := agree
      simp [run,hc] at hread
      have tc : run s c = run t c := ihc (fun k hk => hread k (Or.inl hk))
      have tu : run s u = run t u := ihu (fun k hk => hread k (Or.inr hk))
      simp only [run]
      rw [←tc,←tu]
      simp [hc]

#print axioms traceStable
