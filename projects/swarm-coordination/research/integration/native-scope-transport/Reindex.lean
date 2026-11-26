import Lean

namespace LawReindex

universe u v w
variable {U : Type u} {V : Type v} {E : Type w}

def Enabled (g : E → U → Prop) (tr : List E) (u : U) : Prop :=
  ∀ e, e ∈ tr → g e u

def Pull (f : V → U) (g : E → U → Prop) : E → V → Prop :=
  fun e v => g e (f v)

def Hide (f : U → V) (g : E → U → Prop) : E → V → Prop :=
  fun e v => ∃ u, f u = v ∧ g e u

theorem exact_pull (f : V → U) (g : E → U → Prop) (tr : List E) (v : V) :
    Enabled (Pull f g) tr v ↔ Enabled g tr (f v) := Iff.rfl

theorem hides_every_execution (f : U → V) (g : E → U → Prop) (tr : List E) (u : U) :
    Enabled g tr u → Enabled (Hide f g) tr (f u) := by
  intro h e he
  exact ⟨u,rfl,h e he⟩

theorem disjoint_lifts :
    let f : Bool → Unit := fun _ => ()
    let g : Bool → Bool → Prop := fun e u => e = u
    Enabled (Hide f g) [true,false] () ∧ ¬ ∃ u, Enabled g [true,false] u := by
  dsimp
  constructor
  · intro e _
    exact ⟨e,rfl,rfl⟩
  · rintro ⟨u,h⟩
    have ht := h true (by simp)
    have hf := h false (by simp)
    change true = u at ht
    change false = u at hf
    cases ht.trans hf.symm

#print axioms exact_pull
#print axioms hides_every_execution
#print axioms disjoint_lifts

end LawReindex
