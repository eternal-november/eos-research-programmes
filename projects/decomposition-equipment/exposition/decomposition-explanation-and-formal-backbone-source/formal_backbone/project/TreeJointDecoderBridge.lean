import TreeArrayBridge
import JointQuotientDecoder
set_option backward.isDefEq.respectTransparency false
namespace TreeJointDecoderBridge
open WitnessedDecompositions JointArrayLifting JointQuotientDecoder
variable {V : Type*} [Quiver V] {S : Signature V}
variable {D E : Type*} [Monoid D] [Monoid E]

def Record (active : Component V → Prop) {c : Component V} (t : Tree S c)
    (source : Tree.ActiveLeaf t active → D) (a : t.InputEdge → D) : Prop :=
  (∀ e, ¬active (t.inputEdgeComponent e) → a e = 1) ∧
    ∀ l, eval a (t.leafPath l.val) = source l

theorem exact_tree_decoder (h : D →* E) (inj : Function.Injective h)
    (fc : FactorClosed h) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c) :
    ExactDecoder (Record (D := D) active t) (Record (D := E) active t)
      (fun source l => h (source l)) (fun a e => h (a e)) := by
  intro source target
  constructor
  · intro valid
    obtain ⟨a,ha,_⟩ := Tree.active_source_fixed_coefficient_lift h inj fc active hs t
      source target valid.1 valid.2
    exact ⟨a,⟨fun e he => Tree.lift_inactive h inj ha.1 (valid.1 e he),ha.2⟩,funext ha.1⟩
  · rintro ⟨a,ha,he⟩
    rw [←he]
    constructor
    · intro e he; change h (a e) = 1; rw [ha.1 e he,h.map_one]
    · intro l; rw [←map_eval,ha.2 l]

theorem whole_tree_predicate_preserved (h : D →* E) (inj : Function.Injective h)
    (fc : FactorClosed h) (active : Component V → Prop)
    (hs : Tree.ActiveSignature (S := S) active) {c : Component V} (t : Tree S c)
    (source : Tree.ActiveLeaf t active → D) (test : (t.InputEdge → E) → Prop) :
    (∃ target, Record active t (fun l => h (source l)) target ∧ test target) ↔
      ∃ a, Record active t source a ∧ test (fun e => h (a e)) :=
  joint_test_preserved _ _ _ _ (exact_tree_decoder h inj fc active hs t) test source
end TreeJointDecoderBridge
