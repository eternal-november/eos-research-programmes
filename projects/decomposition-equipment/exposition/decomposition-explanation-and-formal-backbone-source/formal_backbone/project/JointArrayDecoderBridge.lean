import JointArrayLifting
import JointQuotientDecoder
set_option autoImplicit false

/-! Instantiation of the generic exact decoder by the proved joint-array lift.
The skeleton/path data are fixed, and entire edge assignments are retained. -/
namespace JointArrayDecoderBridge
open JointArrayLifting JointQuotientDecoder
universe u v
variable {D : Type u} {E : Type v} [Monoid D] [Monoid E]

/-- A coefficient cut record is one whole shared-edge assignment. -/
def ArrayRecord {A B : Type*} (path : B → List A)
    (source : B → D) (a : A → D) : Prop :=
  ∀ l, eval a (path l) = source l

/-- The full-unital lifting theorem supplies the exact quotient hypothesis.
It is not assumed as an abstract decoder premise. -/
theorem exact_array_decoder {A B : Type*} (h : D →* E)
    (inj : Function.Injective h) (fc : FactorClosed h)
    (path : B → List A) (covered : Covered path) :
    ExactDecoder (ArrayRecord (D := D) path) (ArrayRecord (D := E) path)
      (fun source l => h (source l)) (fun a e => h (a e)) := by
  intro source target
  constructor
  · intro valid
    obtain ⟨a, ha, _⟩ := unique_lift_of_injective_factorClosed h inj fc path covered source target valid
    exact ⟨a, ha.2, funext ha.1⟩
  · rintro ⟨a, ha, he⟩ l
    rw [← he, ← map_eval, ha l]

/-- Every predicate on the complete target cut array is faithfully decoded at
the prescribed source. This includes correlations between different factors. -/
theorem array_predicate_preserved {A B : Type*} (h : D →* E)
    (inj : Function.Injective h) (fc : FactorClosed h)
    (path : B → List A) (covered : Covered path)
    (source : B → D) (test : (A → E) → Prop) :
    (∃ target, ArrayRecord path (fun l => h (source l)) target ∧ test target) ↔
      ∃ a, ArrayRecord path source a ∧ test (fun e => h (a e)) := by
  exact joint_test_preserved _ _ _ _ (exact_array_decoder h inj fc path covered) test source

/-- All retained intermediate word products are transported by the same array;
there is no fresh independent choice for each intermediate observation. -/
theorem intermediate_products_preserved {A K : Type*} (h : D →* E)
    (a : A → D) (words : K → List A) :
    ∀ k, h (eval a (words k)) = eval (fun e => h (a e)) (words k) := by
  intro k
  exact map_eval h a (words k)

end JointArrayDecoderBridge
