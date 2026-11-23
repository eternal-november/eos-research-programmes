module

public import Init

/-! The finite obstruction in §2 of the mixed normal-form reduction report.
The first context is total and the second arrow is a total pure function.
In this case the active set of labels in (5) is the entire first quotient.
-/

public section

namespace ContextualComposition.FiniteDescent

universe u v

/-- A total-domain instance of (3), with a surjective map naming the blocks. -/
structure Presentation (A B Y : Type u) where
  block : B → Y
  onto : ∀ y, ∃ b, block b = y
  selected : A → Y

variable {A B C Y : Type u}

/-- The forgetful observation (4). -/
def Presentation.row (P : Presentation A B Y) (a : A) (b : B) : Prop :=
  P.selected a = P.block b

/-- The gluing arrows for the pushout in (5) under pure postcomposition. -/
inductive Glue (q : B → Y) (g : B → C) : Sum Y C → Sum Y C → Prop where
  | atInput (b : B) : Glue q g (.inl (q b)) (.inr (g b))

abbrev Pushout (q : B → Y) (g : B → C) := Quot (Glue q g)

variable {q : B → Y} {g : B → C}

def left (q : B → Y) (g : B → C) (y : Y) : Pushout q g := Quot.mk _ (.inl y)

def right (q : B → Y) (g : B → C) (c : C) : Pushout q g := Quot.mk _ (.inr c)

theorem glue_eq (b : B) : left q g (q b) = right q g (g b) :=
  Quot.sound (.atInput b)

/-- The mediating map for any compatible pair out of the two legs. -/
def descend {T : Type v} (l : Y → T) (r : C → T) (h : ∀ b, l (q b) = r (g b)) :
    Pushout q g → T :=
  Quot.lift (Sum.elim l r) (by intro x y e; cases e with | atInput b => exact h b)

theorem descend_unique {T : Type v} (l : Y → T) (r : C → T) (h : ∀ b, l (q b) = r (g b))
    (k : Pushout q g → T) (hl : ∀ y, k (left q g y) = l y) (hr : ∀ c, k (right q g c) = r c) :
    k = descend l r h := by
  funext x
  induction x using Quot.ind with
  | _ x => cases x with
           | inl y => exact hl y
           | inr c => exact hr c

/-- Recipe (5) for a pure total continuation with identity output quotient. -/
def Presentation.post (P : Presentation A B Y) (g : B → C) : Presentation A C (Pushout P.block g) where
  block := right P.block g
  onto x := by
    induction x using Quot.ind with
    | _ x => cases x with
             | inr c => exact ⟨c, rfl⟩
             | inl y =>
               obtain ⟨b, rfl⟩ := P.onto y
               exact ⟨g b, (glue_eq b).symm⟩
  selected a := left P.block g (P.selected a)

inductive Middle where | zero | one | two
deriving DecidableEq

def coarsen : Middle → Bool
  | .zero => false
  | .one | .two => true

def continuation : Middle → Bool
  | .zero | .one => false
  | .two => true

def fine : Presentation Unit Middle Middle where
  block := id
  onto y := ⟨y, rfl⟩
  selected _ := .zero

def coarse : Presentation Unit Middle Bool where
  block := coarsen
  onto y := by cases y with
               | false => exact ⟨.zero, rfl⟩
               | true => exact ⟨.one, rfl⟩
  selected _ := false

/-- The quotient-coarsening cell respects both legs and identifies distinct labels. -/
theorem coarsening_cell :
    (∀ b, coarsen (fine.block b) = coarse.block b) ∧
    (∀ a, coarsen (fine.selected a) = coarse.selected a) ∧
    coarsen .one = coarsen .two ∧ Middle.one ≠ Middle.two :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, by decide⟩

theorem same_input : fine.row = coarse.row := by
  funext a b
  cases a
  cases b <;> simp [Presentation.row, fine, coarse, coarsen]

theorem fine_output (a : Unit) (c : Bool) : (fine.post continuation).row a c ↔ c = false := by
  constructor
  · intro h
    exact (congrArg (descend (q := fine.block) (g := continuation) continuation id (fun _ => rfl)) h).symm
  · rintro rfl
    exact glue_eq Middle.zero

theorem coarse_output (a : Unit) (c : Bool) : (coarse.post continuation).row a c := by
  cases c with
  | false => exact glue_eq Middle.zero
  | true =>
    exact (glue_eq (q := coarse.block) (g := continuation) Middle.zero).trans
      ((glue_eq (q := coarse.block) (g := continuation) Middle.one).symm.trans
        (glue_eq (q := coarse.block) (g := continuation) Middle.two))

/-- Even for this fixed pure continuation, no operation on observed relations
can realize the binary recipe on both of the exhibited finite presentations. -/
theorem unused_block_binary_nondescent :
    ¬ ∃ F : (Unit → Middle → Prop) → (Unit → Bool → Prop),
        F fine.row = (fine.post continuation).row ∧ F coarse.row = (coarse.post continuation).row := by
  rintro ⟨F, hf, hc⟩
  have he := hf.symm.trans ((congrArg F same_input).trans hc)
  have hftrue : (fine.post continuation).row () true := he ▸ coarse_output () true
  exact Bool.noConfusion ((fine_output () true).mp hftrue)

end ContextualComposition.FiniteDescent
