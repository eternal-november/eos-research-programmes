module

public import ContextualComposition.FiniteNormalization
import all ContextualComposition.FiniteDescent

/-! Three-stage failure of the finite normalization recipe in §§2 and 5 of
the mixed normal-form reduction report. The middle function and final
restriction realize the pure balancing relation (12) at fixed endpoints.
-/

public section

namespace ContextualComposition.FiniteBalance

open FiniteDescent (left right glue_eq)

inductive B where | b0 | b1 | b2 | b3
deriving DecidableEq

inductive C where | c0 | c1 | c2
deriving DecidableEq

def block : B → Bool
  | .b0 | .b1 => false
  | .b2 | .b3 => true

def middle : B → C
  | .b0 => .c0
  | .b1 | .b2 => .c1
  | .b3 => .c2

def content : FiniteDescent.Presentation Bool B Bool where
  block := block
  onto y := by cases y with
               | false => exact ⟨.b0, rfl⟩
               | true => exact ⟨.b3, rfl⟩
  selected := id

def finalDomain (c : C) : Prop := c = .c2

/-- A contentful arrow followed by a partial map to the singleton. Giving
the domain specifies the latter map uniquely. -/
structure Pair where
  middleCarrier : Type
  label : Type
  first : FiniteDescent.Presentation Bool middleCarrier label
  domain : middleCarrier → Prop

/-- On these pairs the crossing domain in (5) tests membership in the
image of the following domain under the block map. -/
def Pair.crossDomain (p : Pair) (a : Bool) :=
  ∃ b, p.domain b ∧ p.first.selected a = p.first.block b

/-- Each generator identifies native content-pushout along a pure map on
the left with native partial-domain pullback along that same map on the
right. The quotient only imposes these necessary balancing equations. -/
inductive PureBalance : Pair → Pair → Prop where
  | shift {X Y Z : Type} (f : FiniteDescent.Presentation Bool X Y)
      (g : X → Z) (d : Z → Prop) :
      PureBalance ⟨Z, _, f.post g, d⟩ ⟨X, Y, f, fun b => d (g b)⟩

def pushPair : Pair := ⟨C, _, content.post middle, finalDomain⟩
def pullPair : Pair := ⟨B, Bool, content, fun b => finalDomain (middle b)⟩

theorem balanced_representatives : Quot.mk PureBalance pushPair = Quot.mk PureBalance pullPair :=
  Quot.sound (.shift content middle finalDomain)

private theorem push_path (a : Bool) :
    left content.block middle a = right content.block middle C.c2 := by
  cases a with
  | true => exact glue_eq B.b3
  | false =>
    exact (glue_eq (q := content.block) (g := middle) B.b1).trans
      ((glue_eq (q := content.block) (g := middle) B.b2).symm.trans
        (glue_eq (q := content.block) (g := middle) B.b3))

theorem push_domain (a : Bool) : pushPair.crossDomain a :=
  ⟨.c2, rfl, push_path a⟩

theorem pull_domain (a : Bool) : pullPair.crossDomain a ↔ a = true := by
  constructor
  · rintro ⟨b, hb, ha⟩
    cases b <;> simp_all [content, middle, block, finalDomain, pullPair]
  · rintro rfl
    exact ⟨.b3, rfl, rfl⟩

/-- No interpretation of even the quotient by pure shifts can implement the
tested crossing's domain on these two representatives. Any further quotient
that retains their identification inherits the same obstruction. -/
theorem pure_middle_balance_obstruction :
    ¬ ∃ F : Quot PureBalance → Bool → Prop,
      F (Quot.mk _ pushPair) = pushPair.crossDomain ∧
      F (Quot.mk _ pullPair) = pullPair.crossDomain := by
  rintro ⟨F, hp, hq⟩
  have h := hp.symm.trans ((congrArg F balanced_representatives).trans hq)
  have hfalse : pullPair.crossDomain false := h ▸ push_domain false
  exact Bool.noConfusion ((pull_domain false).mp hfalse)

open FiniteNormalization (Presentation)

def firstArrow : Presentation Bool B Bool where
  domain _ := True
  block := content.block
  onto := content.onto
  selected a := content.selected a.val

def pureArrow : Presentation B C C where
  domain _ := True
  block := id
  onto c := ⟨c, rfl⟩
  selected b := middle b.val

def partialArrow : Presentation C Unit Unit where
  domain := finalDomain
  block := id
  onto x := ⟨x, rfl⟩
  selected _ := ()

private theorem comp_domain {A B C Y Z : Type} (p : Presentation A B Y) (q : Presentation B C Z) (a : A) :
    (p.comp q).domain a ↔ ∃ b, q.domain b ∧ p.row a b := by
  constructor
  · rintro ⟨h, ⟨b, hb⟩, he⟩
    exact ⟨b, hb, h, he.symm⟩
  · rintro ⟨b, hb, h, he⟩
    exact ⟨h, ⟨b, hb⟩, he.symm⟩

/-- The three adjacent incidences force the missing corner by difunctionality. -/
theorem intermediate_at_c2 (a : Bool) : (firstArrow.comp pureArrow).row a .c2 := by
  apply (FiniteNormalization.row_comp_iff _ _ _ _).mpr
  refine ⟨trivial, ?_⟩
  intro R hR hEdges
  have edge (b : B) : R (block b) (middle b) := hEdges _ _ ⟨⟨b, trivial⟩, rfl, rfl⟩
  cases a with
  | false => exact hR (edge .b1) (edge .b2) (edge .b3)
  | true => exact edge .b3

private theorem right_middle_domain (b : B) :
    (pureArrow.comp partialArrow).domain b ↔ finalDomain (middle b) := by
  rw [comp_domain]
  constructor
  · rintro ⟨c, hd, _, h⟩
    change middle b = c at h
    exact h ▸ hd
  · intro h
    exact ⟨middle b, h, trivial, rfl⟩

/-- Left bracketing of the actual normalization accepts both source inputs. -/
theorem left_bracket_domain (a : Bool) : ((firstArrow.comp pureArrow).comp partialArrow).domain a :=
  (comp_domain _ _ _).mpr ⟨.c2, rfl, intermediate_at_c2 a⟩

/-- Right bracketing first restricts the middle function to the preimage of c2. -/
theorem right_bracket_domain (a : Bool) : (firstArrow.comp (pureArrow.comp partialArrow)).domain a ↔ a = true := by
  rw [comp_domain]
  constructor
  · rintro ⟨b, hb, _, hab⟩
    exact (pull_domain a).mp ⟨b, (right_middle_domain b).mp hb, hab⟩
  · rintro rfl
    exact ⟨.b3, (right_middle_domain _).mpr rfl, trivial, rfl⟩

/-- Since the domains already differ over the fixed source, even a source-preserving
identification of the two partial presentations cannot be supplied. -/
theorem associativity_domain_obstruction :
    ((firstArrow.comp pureArrow).comp partialArrow).domain ≠
      (firstArrow.comp (pureArrow.comp partialArrow)).domain := by
  intro h
  have ha : (firstArrow.comp (pureArrow.comp partialArrow)).domain false := h ▸ left_bracket_domain false
  exact Bool.noConfusion ((right_bracket_domain false).mp ha)

end ContextualComposition.FiniteBalance
