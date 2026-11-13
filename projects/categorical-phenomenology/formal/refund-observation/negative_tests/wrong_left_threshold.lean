/-
Exact necessary and sufficient local observation regions for two integer stages
with certified lower bounds. The result is universal over all bounded upsets.
-/
import ResourceObservationIff
set_option autoImplicit false
namespace ResourceObservation

def LowerBounded (ell : Int) (U : Profile Int) : Prop :=
  ∀ x, U x → ell ≤ x

def IntWindow (lo hi x : Int) : Prop := lo ≤ x ∧ x ≤ hi

/-- Binary products are observed on every total budget between l+r and C.
Input observations may be arbitrary predicates A and B. Every profile quantified
here is an upward set with its corresponding independently supplied lower bound. -/
def BoundedUniversalAgreement (l r C : Int) (A B : Profile Int) : Prop :=
  ∀ U U' V V' : Profile Int,
    Upward (· ≤ ·) U → Upward (· ≤ ·) U' →
    Upward (· ≤ ·) V → Upward (· ≤ ·) V' →
    LowerBounded l U → LowerBounded l U' →
    LowerBounded r V → LowerBounded r V' →
    AgreeOn A U U' → AgreeOn B V V' →
    AgreeOn (IntWindow (l+r) C)
      (Product Int.add (· ≤ ·) U V) (Product Int.add (· ≤ ·) U' V')

/-- Sufficiency actually holds for all lower-bounded profiles; upward closure
is needed only by the universal necessity direction below. -/
theorem bounded_product_agreement_of_coverage
    (l r C : Int) (A B U U' V V' : Profile Int)
    (coverA : ∀ a, IntWindow l (C+r) a → A a)
    (coverB : ∀ b, IntWindow r (C-l) b → B b)
    (lowU : LowerBounded l U) (lowU' : LowerBounded l U')
    (lowV : LowerBounded r V) (lowV' : LowerBounded r V')
    (sameU : AgreeOn A U U') (sameV : AgreeOn B V V') :
    AgreeOn (IntWindow (l+r) C)
      (Product Int.add (· ≤ ·) U V) (Product Int.add (· ≤ ·) U' V') := by
  intro z hz
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hl := lowU x hx
    have hr := lowV y hy
    have hxA : A x := coverA x ⟨hl, by
      change x + y ≤ z at hxy
      have hC := hz.2
      omega⟩
    have hyB : B y := coverB y ⟨hr, by
      change x + y ≤ z at hxy
      have hC := hz.2
      omega⟩
    exact ⟨x, y, (sameU x hxA).mp hx, (sameV y hyB).mp hy, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hl := lowU' x hx
    have hr := lowV' y hy
    have hxA : A x := coverA x ⟨hl, by
      change x + y ≤ z at hxy
      have hC := hz.2
      omega⟩
    have hyB : B y := coverB y ⟨hr, by
      change x + y ≤ z at hxy
      have hC := hz.2
      omega⟩
    exact ⟨x, y, (sameU x hxA).mpr hx, (sameV y hyB).mpr hy, hxy⟩

/-- Necessity of the first shifted window. The proof uses a principal upset
and its observation-generated upward subset, not a decidability assumption. -/
theorem bounded_agreement_forces_left_coverage
    (l r C : Int) (A B : Profile Int)
    (agreement : BoundedUniversalAgreement l r C A B) :
    ∀ a, IntWindow l (C-r) a → A a := by
  intro a ha
  have boundPrincipal : LowerBounded l (Principal (fun x y : Int => x ≤ y) a) := by
    intro x hx
    exact Int.le_trans ha.1 hx
  have boundObserved : LowerBounded l (ObservedPrincipal (fun x y : Int => x ≤ y) A a) := by
    rintro x ⟨c, _, hac, hcx⟩
    exact Int.le_trans ha.1 (Int.le_trans hac hcx)
  have boundR : LowerBounded r (Principal (fun x y : Int => x ≤ y) r) :=
    fun _ hx => hx
  have same := agreement
    (Principal (· ≤ ·) a) (ObservedPrincipal (· ≤ ·) A a)
    (Principal (· ≤ ·) r) (Principal (· ≤ ·) r)
    (principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) a)
    (observed_principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) A a)
    (principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) r)
    (principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) r)
    boundPrincipal boundObserved boundR boundR
    (principal_agrees_observed (· ≤ ·) Int.le_refl (fun {_ _ _} => Int.le_trans) A a)
    (fun _ _ => Iff.rfl)
  have inOutput : IntWindow (l+r) C (a+r) := by
    obtain ⟨hla, hac⟩ := ha
    constructor <;> omega
  have original : Product Int.add (· ≤ ·) (Principal (· ≤ ·) a) (Principal (· ≤ ·) r) (a+r) :=
    ⟨a, r, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩
  rcases (same (a+r) inOutput).mp original with ⟨x, y, hx, hy, hxy⟩
  rcases hx with ⟨c, hcA, hac, hcx⟩
  change r ≤ y at hy
  change x + y ≤ a + r at hxy
  have hca : c = a := by omega
  exact hca ▸ hcA

/-- Necessity of the second shifted window. -/
theorem bounded_agreement_forces_right_coverage
    (l r C : Int) (A B : Profile Int)
    (agreement : BoundedUniversalAgreement l r C A B) :
    ∀ b, IntWindow r (C-l) b → B b := by
  intro b hb
  have boundPrincipal : LowerBounded r (Principal (fun x y : Int => x ≤ y) b) := by
    intro y hy
    exact Int.le_trans hb.1 hy
  have boundObserved : LowerBounded r (ObservedPrincipal (fun x y : Int => x ≤ y) B b) := by
    rintro y ⟨c, _, hbc, hcy⟩
    exact Int.le_trans hb.1 (Int.le_trans hbc hcy)
  have boundL : LowerBounded l (Principal (fun x y : Int => x ≤ y) l) :=
    fun _ hx => hx
  have same := agreement
    (Principal (· ≤ ·) l) (Principal (· ≤ ·) l)
    (Principal (· ≤ ·) b) (ObservedPrincipal (· ≤ ·) B b)
    (principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) l)
    (principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) l)
    (principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) b)
    (observed_principal_upward (· ≤ ·) (fun {_ _ _} => Int.le_trans) B b)
    boundL boundL boundPrincipal boundObserved
    (fun _ _ => Iff.rfl)
    (principal_agrees_observed (· ≤ ·) Int.le_refl (fun {_ _ _} => Int.le_trans) B b)
  have inOutput : IntWindow (l+r) C (l+b) := by
    obtain ⟨hrb, hbc⟩ := hb
    constructor <;> omega
  have original : Product Int.add (· ≤ ·) (Principal (· ≤ ·) l) (Principal (· ≤ ·) b) (l+b) :=
    ⟨l, b, Int.le_refl _, Int.le_refl _, Int.le_refl _⟩
  rcases (same (l+b) inOutput).mp original with ⟨x, y, hx, hy, hxy⟩
  rcases hy with ⟨c, hcB, hbc, hcy⟩
  change l ≤ x at hx
  change x + y ≤ l + b at hxy
  have hcb : c = b := by omega
  exact hcb ▸ hcB

/-- Exact two-stage integer boundary, including C < l+r (all windows empty).
Every relevant local point is necessary for universal determination of all
output-budget observations; this is not a per-instance optimum query bound. -/
theorem bounded_universal_agreement_iff_coverage
    (l r C : Int) (A B : Profile Int) :
    BoundedUniversalAgreement l r C A B ↔
      (∀ a, IntWindow l (C-r) a → A a) ∧
      (∀ b, IntWindow r (C-l) b → B b) := by
  constructor
  · intro agreement
    exact ⟨bounded_agreement_forces_left_coverage l r C A B agreement,
      bounded_agreement_forces_right_coverage l r C A B agreement⟩
  · rintro ⟨coverA, coverB⟩ U U' V V' _ _ _ _ lowU lowU' lowV lowV' sameU sameV
    exact bounded_product_agreement_of_coverage l r C A B U U' V V'
      coverA coverB lowU lowU' lowV lowV' sameU sameV

theorem shifted_windows_suffice (l r C : Int) :
    BoundedUniversalAgreement l r C (IntWindow l (C-r)) (IntWindow r (C-l)) :=
  (bounded_universal_agreement_iff_coverage l r C _ _).mpr
    ⟨fun _ h => h, fun _ h => h⟩

/-- The report's example: lower bounds -2 and 1, total C=3, local windows
[-2,2] and [1,5], output [-1,3]. -/
theorem numerical_shifted_windows_suffice :
    BoundedUniversalAgreement (-2) 1 3 (IntWindow (-2) 2) (IntWindow 1 5) :=
  shifted_windows_suffice (-2) 1 3

/-- Applying the total cap 3 independently to both stages is invalid. Stage 2
budget 5 is required because the first stage can contribute the credit -2. -/
theorem naive_total_cap_fails :
    ¬ BoundedUniversalAgreement (-2) 1 3 (IntWindow (-2) 3) (IntWindow 1 3) := by
  intro agreement
  have covers := (bounded_universal_agreement_iff_coverage (-2) 1 3
    (IntWindow (-2) 3) (IntWindow 1 3)).mp agreement
  have h5 : IntWindow 1 3 5 := covers.2 5 ⟨by decide, by decide⟩
  exact (by decide : ¬ ((5 : Int) ≤ 3)) h5.2

#print axioms bounded_product_agreement_of_coverage
#print axioms bounded_agreement_forces_left_coverage
#print axioms bounded_agreement_forces_right_coverage
#print axioms bounded_universal_agreement_iff_coverage
#print axioms shifted_windows_suffice
#print axioms numerical_shifted_windows_suffice
#print axioms naive_total_cap_fails
end ResourceObservation
