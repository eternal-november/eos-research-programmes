/- Antisymmetry is necessary for the literal membership conclusion. -/
import ResourceObservationIff
set_option autoImplicit false
namespace ResourceObservation

def BoolIndiscrete (_ _ : Bool) : Prop := True

-- XOR is an abelian group operation with identity false and self-inverses.
theorem bool_xor_group_laws :
    (∀ a b c : Bool, Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c)) ∧
    (∀ a b : Bool, Bool.xor a b = Bool.xor b a) ∧
    (∀ a : Bool, Bool.xor a false = a) ∧
    (∀ a : Bool, Bool.xor a a = false) := by decide

theorem indiscrete_translation_invariant_preorder :
    (∀ a : Bool, BoolIndiscrete a a) ∧
    (∀ a b c : Bool, BoolIndiscrete a b → BoolIndiscrete b c → BoolIndiscrete a c) ∧
    (∀ a b c : Bool, BoolIndiscrete a b →
      BoolIndiscrete (Bool.xor a c) (Bool.xor b c)) :=
  ⟨fun _ => True.intro, fun _ _ _ _ _ => True.intro, fun _ _ _ _ => True.intro⟩

theorem indiscrete_not_antisymmetric :
    ¬ (∀ a b : Bool, BoolIndiscrete a b → BoolIndiscrete b a → a = b) := by
  intro h
  have impossible := h false true True.intro True.intro
  cases impossible

-- One point suffices to observe every indiscrete upset, but B is not all.
theorem preorder_nonempty_proper_compositional :
    UniversalProductAgreement Bool.xor BoolIndiscrete (fun b => b = true) ∧
    (∃ b : Bool, b = true) ∧ ¬ (∀ b : Bool, b = true) := by
  refine ⟨?_, ⟨true, rfl⟩, ?_⟩
  · intro U U' V V' upU upU' upV upV' sameU sameV
    apply observed_product_congruence Bool.xor BoolIndiscrete (fun b => b = true)
      U U' V V' ?_ upU upU' upV upV' sameU sameV
    intro b _ x y _
    exact ⟨true, true, rfl, rfl, True.intro, True.intro, True.intro⟩
  · intro all
    have impossible := all false
    cases impossible

#print axioms bool_xor_group_laws
#print axioms indiscrete_translation_invariant_preorder
#print axioms indiscrete_not_antisymmetric
#print axioms preorder_nonempty_proper_compositional
end ResourceObservation
