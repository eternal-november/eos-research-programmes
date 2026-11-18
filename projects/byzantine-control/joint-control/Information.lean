import Std

/-! Discrete logical core of INFORMATION.md. Real inequalities, median
counting, polygon geometry and physical applicability have prose proofs there.
This file uses no sorry or project-specific axioms. -/
namespace JointInformation

def Candidate {I X : Type} (F : (I → Prop) → Prop)
    (row : I → X → Prop) (x : X) : Prop :=
  ∃ S, F S ∧ ∀ i, ¬ S i → row i x

theorem actual_candidate {I X : Type} (F : (I → Prop) → Prop)
    (row : I → X → Prop) (x : X) (S : I → Prop)
    (admitted : F S) (sound : ∀ i, ¬ S i → row i x) :
    Candidate F row x := ⟨S, admitted, sound⟩

/- The separating object is a whole bundle, not one individually sufficient row.
Bundle may instantiate two independent partial rows or a rectangular frame. -/
theorem common_bundle_transfer {I X T : Type} (F : (I → Prop) → Prop)
    (row : I → X → Prop) (member : T → I → Prop) (bound : X → X → Prop)
    (overlap : ∀ S S', F S → F S' →
      ∃ bundle, ∀ i, member bundle i → ¬ S i ∧ ¬ S' i)
    (separates : ∀ bundle x y,
      (∀ i, member bundle i → row i x) →
      (∀ i, member bundle i → row i y) → bound x y)
    (x y : X) (hx : Candidate F row x) (hy : Candidate F row y) : bound x y := by
  obtain ⟨S, hS, hxr⟩ := hx
  obtain ⟨S', hS', hyr⟩ := hy
  obtain ⟨bundle, hb⟩ := overlap S S' hS hS'
  exact separates bundle x y
    (fun i hi => hxr i (hb i hi).1)
    (fun i hi => hyr i (hb i hi).2)

def MapUnion {G I : Type} (allowed : G → Prop)
    (family : G → (I → Prop) → Prop) (S : I → Prop) : Prop :=
  ∃ g, allowed g ∧ family g S

theorem hidden_map_inclusion {G I X : Type} (allowed : G → Prop)
    (family : G → (I → Prop) → Prop) (row : I → X → Prop)
    (g : G) (hg : allowed g) (x : X) (hx : Candidate (family g) row x) :
    Candidate (MapUnion allowed family) row x := by
  obtain ⟨S, hS, hrow⟩ := hx
  exact ⟨S, ⟨g, hg, hS⟩, hrow⟩

theorem conservative_enlargement {I X : Type}
    (F F' : (I → Prop) → Prop) (row row' : I → X → Prop)
    (domains : ∀ S, F S → F' S) (widen : ∀ i x, row i x → row' i x)
    (x : X) (hx : Candidate F row x) : Candidate F' row' x := by
  obtain ⟨S, hS, hr⟩ := hx
  exact ⟨S, domains S hS, fun i hi => widen i x (hr i hi)⟩

theorem duplicate_explanations_prevent_decoding {X Y : Type}
    (possible : X → Y → Prop) (x x' : X) (y : Y)
    (different : x ≠ x') (hx : possible x y) (hx' : possible x' y) :
    ¬ ∃ decode : Y → X, ∀ z report, possible z report → decode report = z := by
  rintro ⟨decode, correct⟩
  exact different ((correct x y hx).symm.trans (correct x' y hx'))

theorem age_from_schedule (request sample result budget : Nat)
    (after_request : request ≤ sample) (by_deadline : result ≤ request + budget) :
    result - sample ≤ budget := by omega

theorem first_fresh_after_reset : (12 : Nat) + 8 ≤ 20 := by decide

theorem held_sample_age (round t : Nat)
    (before_next : t < round + 18) : t - (round + 1) ≤ 16 := by omega

#print axioms actual_candidate
#print axioms common_bundle_transfer
#print axioms hidden_map_inclusion
#print axioms conservative_enlargement
#print axioms duplicate_explanations_prevent_decoding
#print axioms age_from_schedule
#print axioms first_fresh_after_reset
#print axioms held_sample_age
end JointInformation
