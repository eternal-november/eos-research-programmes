import Execution

/- Clock-free compatibility of prescriptions on all reachable local views.
   The construction adds no global depth or fault input to the supplied local view.
   This is a compatibility
   theorem for a supplied sequence, not an unrestricted synthesis algorithm. -/
namespace ByzantineControlIntegration
open ByzantineControlProgram

def CrossCompatible (M : Model I X H A F) (K : Nat → Family F X)
    (p : Nat → Policy I H A) : Prop :=
  ∀ t s f g x y i, K t f x → K s g y → M.correct f i → M.correct g i →
    M.observe i x = M.observe i y →
    p t i (M.observe i x) = p s i (M.observe i y)

def Represents (M : Model I X H A F) (K : Nat → Family F X)
    (p : Nat → Policy I H A) (q : Policy I H A) : Prop :=
  ∀ t f x i, K t f x → M.correct f i →
    q i (M.observe i x) = p t i (M.observe i x)

theorem represents_compatible (M : Model I X H A F) (K : Nat → Family F X)
    (p : Nat → Policy I H A) (q : Policy I H A)
    (hq : Represents M K p q) : CrossCompatible M K p := by
  intro t s f g x y i hx hy hc hd he
  rw [← hq t f x i hx hc, ← hq s g y i hy hd, he]

/- Depth is retained in the analyst's occurrence carrier, then forgotten by every
   local observation. Existing factorization supplies the actual local policy. -/
theorem compatible_representable (M : Model I X H A F) (K : Nat → Family F X)
    (p : Nat → Policy I H A) (fallback : (i : I) → A i)
    (hc : CrossCompatible M K p) :
    ∃ q : Policy I H A, Represents M K p q := by
  let Occ : Model I (Nat × X) H A F := {
    observe := fun i tx => M.observe i tx.2
    correct := M.correct
    initial := fun f tx => K tx.1 f tx.2
    next := fun _ _ _ _ => False }
  let D : Family F (Nat × X) := fun f tx => K tx.1 f tx.2
  let issued : (i : I) → F → (Nat × X) → A i :=
    fun i _ tx => p tx.1 i (M.observe i tx.2)
  have uniform : ∀ i f g x y, D f x → D g y →
      Occ.correct f i → Occ.correct g i →
      Occ.observe i x = Occ.observe i y → issued i f x = issued i g y := by
    intro i f g x y hx hy hf hg he
    exact hc x.1 y.1 f g x.2 y.2 i hx hy hf hg he
  obtain ⟨q, hq⟩ := local_policy_factorization Occ D issued fallback uniform
  refine ⟨q, ?_⟩
  intro t f x i hx hi
  exact hq i f (t,x) hx hi

theorem compatible_iff_representable (M : Model I X H A F)
    (K : Nat → Family F X) (p : Nat → Policy I H A)
    (fallback : (i : I) → A i) :
    CrossCompatible M K p ↔ ∃ q : Policy I H A, Represents M K p q := by
  constructor
  · exact compatible_representable M K p fallback
  · rintro ⟨q,hq⟩
    exact represents_compatible M K p q hq

theorem represented_follows (M : Model I X H A F) (K : Nat → Family F X)
    (p : Nat → Policy I H A) (q : Policy I H A)
    (hq : Represents M K p q) (t : Nat) (f : F) (x : X)
    (hx : K t f x) (a : (i : I) → A i) :
    Follows M f q x a ↔ Follows M f (p t) x a := by
  constructor <;> intro h i hi
  · rw [← hq t f x i hx hi]
    exact h i hi
  · rw [hq t f x i hx hi]
    exact h i hi

theorem represented_step (M : Model I X H A F) (K : Nat → Family F X)
    (p : Nat → Policy I H A) (q : Policy I H A)
    (hq : Represents M K p q) (t : Nat) (f : F) (x y : X)
    (hx : K t f x) :
    Step M f q x y ↔ Step M f (p t) x y := by
  constructor
  · rintro ⟨a,ha,hn⟩
    exact ⟨a,(represented_follows M K p q hq t f x hx a).mp ha,hn⟩
  · rintro ⟨a,ha,hn⟩
    exact ⟨a,(represented_follows M K p q hq t f x hx a).mpr ha,hn⟩

/- Equality of ALL reachable families rules out extra compiled-policy branches. -/
theorem represented_reach (M : Model I X H A F) (K : Family F X)
    (p : Nat → Policy I H A) (q : Policy I H A)
    (hq : Represents M (Reach M K p) p q) :
    ∀ t f x, Reach M K (fun _ => q) t f x ↔ Reach M K p t f x := by
  intro t
  induction t with
  | zero => intro f x; rfl
  | succ t ih =>
    intro f y
    constructor
    · rintro ⟨x,hx,hs⟩
      have old : Reach M K p t f x := (ih f x).mp hx
      exact ⟨x,old,(represented_step M (Reach M K p) p q hq t f x y old).mp hs⟩
    · rintro ⟨x,hx,hs⟩
      exact ⟨x,(ih f x).mpr hx,
        (represented_step M (Reach M K p) p q hq t f x y hx).mpr hs⟩

theorem compatible_safety_transport (M : Model I X H A F) (K S : Family F X)
    (p : Nat → Policy I H A) (fallback : (i : I) → A i)
    (hc : CrossCompatible M (Reach M K p) p)
    (safe : ∀ t, AllSafe (Reach M K p t) S) :
    ∃ q : Policy I H A, ∀ t, AllSafe (Reach M K (fun _ => q) t) S := by
  obtain ⟨q,hq⟩ := compatible_representable M (Reach M K p) p fallback hc
  refine ⟨q,?_⟩
  intro t f x hx
  exact safe t f x ((represented_reach M K p q hq t f x).mp hx)

theorem represented_nonblocking (M : Model I X H A F) (K : Family F X)
    (p : Nat → Policy I H A) (q : Policy I H A)
    (hq : Represents M (Reach M K p) p q)
    (nb : ∀ t, Nonblocking M (Reach M K p t) (p t)) :
    ∀ t, Nonblocking M (Reach M K (fun _ => q) t) q := by
  intro t f x hx a ha
  have old := (represented_reach M K p q hq t f x).mp hx
  exact nb t f x old a
    ((represented_follows M (Reach M K p) p q hq t f x old a).mp ha)

/- Formal witness: a stage-indexed plan can disagree on the very same local view.
   This is a prescription-compilation obstruction, not a complete physical model. -/
theorem stage_choices_need_not_be_compatible :
    ¬ ∃ q : Unit → Bool, q () = false ∧ q () = true := by
  rintro ⟨q,hf,ht⟩
  have impossible : false = true := hf.symm.trans ht
  cases impossible

#print axioms compatible_iff_representable
#print axioms represented_follows
#print axioms represented_step
#print axioms represented_reach
#print axioms compatible_safety_transport
#print axioms represented_nonblocking
#print axioms stage_choices_need_not_be_compatible
end ByzantineControlIntegration
