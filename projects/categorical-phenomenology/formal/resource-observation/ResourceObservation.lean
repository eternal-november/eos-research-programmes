/-
Hand-written formalization of the resource-observation sufficiency argument.
This is separate from literal replay of machine-generated list certificates.
It assumes an explicit arithmetic witness condition, not compositionality.
The relation and composition are arbitrary; the theorem therefore specializes
in particular to every commutative ordered monoid, finite or infinite.
-/
import Std
set_option autoImplicit false
universe u
namespace ResourceObservation
variable {M : Type u}

abbrev Profile (M : Type u) := M → Prop

def Upward (le : M → M → Prop) (U : Profile M) : Prop :=
  ∀ ⦃x y : M⦄, U x → le x y → U y

def Product (add : M → M → M) (le : M → M → Prop)
    (U V : Profile M) (b : M) : Prop :=
  ∃ x y, U x ∧ V y ∧ le (add x y) b

def Restrict (B U : Profile M) : Profile M :=
  fun x => B x ∧ U x

def AgreeOn (B U V : Profile M) : Prop :=
  ∀ b, B b → (U b ↔ V b)

-- The hypothesis only mentions the arithmetic, B, and factor witnesses.
-- It does not quantify over unknown resource profiles or assume the conclusion.
def ObservedFactorDomination (add : M → M → M) (le : M → M → Prop)
    (B : Profile M) : Prop :=
  ∀ b, B b → ∀ x y, le (add x y) b →
    ∃ a c, B a ∧ B c ∧ le x a ∧ le y c ∧ le (add a c) b

-- Exact restriction identity at each observed output budget.
theorem restriction_product_exact
    (add : M → M → M) (le : M → M → Prop)
    (B U V : Profile M)
    (factor : ObservedFactorDomination add le B)
    (upU : Upward le U) (upV : Upward le V)
    (b : M) (hb : B b) :
    Product add le U V b ↔
      Product add le (Restrict B U) (Restrict B V) b := by
  constructor
  · intro h
    rcases h with ⟨x, y, hx, hy, hxy⟩
    rcases factor b hb x y hxy with ⟨a, c, ha, hc, hxa, hyc, hac⟩
    exact ⟨a, c, ⟨ha, upU hx hxa⟩, ⟨hc, upV hy hyc⟩, hac⟩
  · intro h
    rcases h with ⟨a, c, ha, hc, hac⟩
    exact ⟨a, c, ha.2, hc.2, hac⟩

-- Agreement preservation for upward inputs. For a transitive order, Product
-- is itself upward (proved below), so this is a congruence on upward profiles.
theorem observed_product_congruence
    (add : M → M → M) (le : M → M → Prop)
    (B U U' V V' : Profile M)
    (factor : ObservedFactorDomination add le B)
    (upU : Upward le U) (upU' : Upward le U')
    (upV : Upward le V) (upV' : Upward le V')
    (sameU : AgreeOn B U U') (sameV : AgreeOn B V V') :
    AgreeOn B (Product add le U V) (Product add le U' V') := by
  intro b hb
  constructor
  · intro h
    rcases (restriction_product_exact add le B U V factor upU upV b hb).mp h with
      ⟨a, c, ha, hc, hac⟩
    exact ⟨a, c, (sameU a ha.1).mp ha.2, (sameV c hc.1).mp hc.2, hac⟩
  · intro h
    rcases (restriction_product_exact add le B U' V' factor upU' upV' b hb).mp h with
      ⟨a, c, ha, hc, hac⟩
    exact ⟨a, c, (sameU a ha.1).mpr ha.2, (sameV c hc.1).mpr hc.2, hac⟩

-- Closure needs transitivity of the relation; it is not asserted for an
-- arbitrary relation merely because agreement preservation holds.
theorem product_upward_of_trans
    (add : M → M → M) (le : M → M → Prop)
    (trans : ∀ ⦃a b c : M⦄, le a b → le b c → le a c)
    (U V : Profile M) : Upward le (Product add le U V) := by
  intro b c hb hbc
  rcases hb with ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, trans hxy hbc⟩

-- A checkable stronger arithmetic condition, with witnesses a=x and c=y.
theorem factor_closed_suffices
    (add : M → M → M) (le : M → M → Prop) (B : Profile M)
    (refl : ∀ x, le x x)
    (closed : ∀ b, B b → ∀ x y, le (add x y) b → B x ∧ B y) :
    ObservedFactorDomination add le B := by
  intro b hb x y hxy
  exact ⟨x, y, (closed b hb x y hxy).1, (closed b hb x y hxy).2,
    refl x, refl y, hxy⟩

-- Concrete family: every finite natural-number budget initial segment.
theorem nat_initial_segment_factor_domination (limit : Nat) :
    ObservedFactorDomination Nat.add (· ≤ ·) (fun b => b ≤ limit) := by
  apply factor_closed_suffices Nat.add (· ≤ ·) (fun b => b ≤ limit) Nat.le_refl
  intro b hb x y hxy
  exact ⟨Nat.le_trans (Nat.le_trans (Nat.le_add_right x y) hxy) hb,
    Nat.le_trans (Nat.le_trans (Nat.le_add_left y x) hxy) hb⟩

theorem nat_budget_observations_compose
    (limit : Nat) (U U' V V' : Profile Nat)
    (upU : Upward (· ≤ ·) U) (upU' : Upward (· ≤ ·) U')
    (upV : Upward (· ≤ ·) V) (upV' : Upward (· ≤ ·) V')
    (sameU : AgreeOn (fun b => b ≤ limit) U U')
    (sameV : AgreeOn (fun b => b ≤ limit) V V') :
    AgreeOn (fun b => b ≤ limit)
      (Product Nat.add (· ≤ ·) U V) (Product Nat.add (· ≤ ·) U' V') :=
  observed_product_congruence Nat.add (· ≤ ·) (fun b => b ≤ limit)
    U U' V V' (nat_initial_segment_factor_domination limit)
    upU upU' upV upV' sameU sameV

-- A finite non-downward-closed observation domain can satisfy the criterion.
-- Bool with false < true and addition = OR is the two-element max monoid.
def BoolLE (a b : Bool) : Prop := a = false ∨ b = true
def OnlyTop (b : Bool) : Prop := b = true

theorem bool_top_factor_domination :
    ObservedFactorDomination Bool.or BoolLE OnlyTop := by
  intro b hb x y _
  exact ⟨true, true, rfl, rfl, Or.inr rfl, Or.inr rfl, Or.inr hb⟩

theorem bool_top_not_downward_closed :
    ¬ (∀ (a b : Bool), BoolLE a b → OnlyTop b → OnlyTop a) := by
  intro h
  have impossible : false = true := h false true (Or.inl rfl) rfl
  cases impossible

-- Concrete negative control: a single observation at budget 2 is not enough
-- for ordinary addition. The missing hypothesis is factor domination.
def AtLeastOne (b : Nat) : Prop := 1 ≤ b
def AtLeastTwo (b : Nat) : Prop := 2 ≤ b
def OnlyTwo (b : Nat) : Prop := b = 2

theorem nat_nonlower_counterexample :
    Upward (· ≤ ·) AtLeastOne ∧ Upward (· ≤ ·) AtLeastTwo ∧
    AgreeOn OnlyTwo AtLeastOne AtLeastTwo ∧
    Product Nat.add (· ≤ ·) AtLeastOne AtLeastOne 2 ∧
    ¬ Product Nat.add (· ≤ ·) AtLeastTwo AtLeastOne 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    exact Nat.le_trans hx hxy
  · intro x y hx hxy
    exact Nat.le_trans hx hxy
  · intro b hb
    change b = 2 at hb
    cases hb
    exact ⟨fun _ => Nat.le_refl 2, fun _ => Nat.le_add_right 1 1⟩
  · exact ⟨1, 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 2⟩
  · intro h
    rcases h with ⟨x, y, hx, hy, hxy⟩
    have impossible : 3 ≤ 2 := Nat.le_trans (Nat.add_le_add hx hy) hxy
    exact (by decide : ¬ (3 ≤ 2)) impossible

theorem nat_nonlower_factor_domination_fails :
    ¬ ObservedFactorDomination Nat.add (· ≤ ·) OnlyTwo := by
  intro h
  rcases h 2 rfl 1 1 (Nat.le_refl 2) with ⟨a, c, ha, hc, _, _, hac⟩
  change a = 2 at ha
  change c = 2 at hc
  cases ha
  cases hc
  exact (by decide : ¬ (4 ≤ 2)) hac

#print axioms nat_nonlower_counterexample
#print axioms nat_nonlower_factor_domination_fails
#print axioms restriction_product_exact
#print axioms observed_product_congruence
#print axioms product_upward_of_trans
#print axioms factor_closed_suffices
#print axioms nat_initial_segment_factor_domination
#print axioms nat_budget_observations_compose
#print axioms bool_top_factor_domination
#print axioms bool_top_not_downward_closed
end ResourceObservation
