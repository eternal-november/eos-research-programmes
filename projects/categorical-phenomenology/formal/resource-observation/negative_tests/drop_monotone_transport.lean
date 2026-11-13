/-
Separate manual extension: exact factor-observation criterion, both directions.
The assumptions are a reflexive, transitive relation and a monotone binary
operation. No finiteness, commutativity, associativity or antisymmetry is used.
In particular, this specializes to ordered commutative resource monoids.
-/
import ResourceObservation
set_option autoImplicit false
universe u
namespace ResourceObservation
variable {M : Type u}

def Principal (le : M → M → Prop) (x : M) : Profile M := le x

def ObservedPrincipal (le : M → M → Prop) (B : Profile M) (x : M) : Profile M :=
  fun y => ∃ a, B a ∧ le x a ∧ le a y

def UniversalProductAgreement
    (add : M → M → M) (le : M → M → Prop) (B : Profile M) : Prop :=
  ∀ (U U' V V' : Profile M),
    Upward le U → Upward le U' → Upward le V → Upward le V' →
    AgreeOn B U U' → AgreeOn B V V' →
    AgreeOn B (Product add le U V) (Product add le U' V')

def UniversalRestrictionExact
    (add : M → M → M) (le : M → M → Prop) (B : Profile M) : Prop :=
  ∀ (U V : Profile M), Upward le U → Upward le V →
    ∀ b, B b → (Product add le U V b ↔
      Product add le (Restrict B U) (Restrict B V) b)

theorem principal_upward
    (le : M → M → Prop)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c) (x : M) :
    Upward le (Principal le x) := by
  intro a b hxa hab
  exact trans hxa hab

theorem observed_principal_upward
    (le : M → M → Prop)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (B : Profile M) (x : M) : Upward le (ObservedPrincipal le B x) := by
  intro a b ha hab
  rcases ha with ⟨c, hc, hxc, hca⟩
  exact ⟨c, hc, hxc, trans hca hab⟩

theorem principal_agrees_observed
    (le : M → M → Prop) (refl : ∀ x, le x x)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (B : Profile M) (x : M) :
    AgreeOn B (Principal le x) (ObservedPrincipal le B x) := by
  intro b hb
  constructor
  · intro hxb
    exact ⟨b, hb, hxb, refl b⟩
  · intro h
    rcases h with ⟨a, _, hxa, hab⟩
    exact trans hxa hab

-- Necessity: use principal profiles and their observed upward saturations.
-- Universal agreement is the antecedent of the implication being proved,
-- not an unproved assumption of the final biconditional theorem.
theorem factor_domination_of_universal_agreement
    (add : M → M → M) (le : M → M → Prop)
    (refl : ∀ x, le x x)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (mono : ∀ ⦃a a' c c' : M⦄, le a a' → le c c' → le (add a c) (add a' c'))
    (B : Profile M) (agreement : UniversalProductAgreement add le B) :
    ObservedFactorDomination add le B := by
  intro b hb x y hxy
  have h := agreement (Principal le x) (ObservedPrincipal le B x)
    (Principal le y) (ObservedPrincipal le B y)
    (principal_upward le trans x) (observed_principal_upward le trans B x)
    (principal_upward le trans y) (observed_principal_upward le trans B y)
    (principal_agrees_observed le refl trans B x)
    (principal_agrees_observed le refl trans B y) b hb
  have original : Product add le (Principal le x) (Principal le y) b :=
    ⟨x, y, refl x, refl y, hxy⟩
  rcases h.mp original with ⟨x', y', hx', hy', hsum⟩
  rcases hx' with ⟨a, ha, hxa, hax'⟩
  rcases hy' with ⟨c, hc, hyc, hcy'⟩
  exact ⟨a, c, ha, hc, hxa, hyc, hsum⟩

theorem universal_product_agreement_iff_factor
    (add : M → M → M) (le : M → M → Prop)
    (refl : ∀ x, le x x)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (mono : ∀ ⦃a a' c c' : M⦄, le a a' → le c c' → le (add a c) (add a' c'))
    (B : Profile M) :
    UniversalProductAgreement add le B ↔ ObservedFactorDomination add le B := by
  constructor
  · exact factor_domination_of_universal_agreement add le refl trans mono B
  · intro factor U U' V V' upU upU' upV upV' sameU sameV
    exact observed_product_congruence add le B U U' V V' factor
      upU upU' upV upV' sameU sameV

-- The restriction identity also characterizes the arithmetic condition.
theorem universal_restriction_exact_iff_factor
    (add : M → M → M) (le : M → M → Prop)
    (refl : ∀ x, le x x)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (B : Profile M) :
    UniversalRestrictionExact add le B ↔ ObservedFactorDomination add le B := by
  constructor
  · intro restriction b hb x y hxy
    have original : Product add le (Principal le x) (Principal le y) b :=
      ⟨x, y, refl x, refl y, hxy⟩
    have restricted := (restriction (Principal le x) (Principal le y)
      (principal_upward le trans x) (principal_upward le trans y) b hb).mp original
    rcases restricted with ⟨a, c, ha, hc, hac⟩
    exact ⟨a, c, ha.1, hc.1, ha.2, hc.2, hac⟩
  · intro factor U V upU upV b hb
    exact restriction_product_exact add le B U V factor upU upV b hb

theorem universal_agreement_iff_restriction_exact
    (add : M → M → M) (le : M → M → Prop)
    (refl : ∀ x, le x x)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (mono : ∀ ⦃a a' c c' : M⦄, le a a' → le c c' → le (add a c) (add a' c'))
    (B : Profile M) :
    UniversalProductAgreement add le B ↔ UniversalRestrictionExact add le B :=
  Iff.trans (universal_product_agreement_iff_factor add le refl trans mono B)
    (Iff.symm (universal_restriction_exact_iff_factor add le refl trans B))

#print axioms principal_upward
#print axioms observed_principal_upward
#print axioms principal_agrees_observed
#print axioms factor_domination_of_universal_agreement
#print axioms universal_product_agreement_iff_factor
#print axioms universal_restriction_exact_iff_factor
#print axioms universal_agreement_iff_restriction_exact
end ResourceObservation
