import Std

/-!
D1 finite typed action. This standalone L slice uses Lean's core/Std only.
It does NOT claim to import the original WitnessedDecompositions API.
The accompanying P adapter identifies its typed relation cells, binary witnesses,
occurrence forests and invariant rotations with that API.
-/
namespace D1FiniteTypedAction

inductive Interface where | A | B | C
  deriving DecidableEq, Repr
inductive Point where | zero | one | two
  deriving DecidableEq, Repr

/-- Actual carrier bijections, including their inverse laws. -/
structure Perm where
  forward : Point → Point
  backward : Point → Point
  backward_forward : ∀ x, backward (forward x) = x
  forward_backward : ∀ x, forward (backward x) = x

namespace Perm

def identity : Perm := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
/-- `then p q` means first p, then q. -/
def sequence (p q : Perm) : Perm where
  forward x := q.forward (p.forward x)
  backward x := p.backward (q.backward x)
  backward_forward x := by rw [q.backward_forward, p.backward_forward]
  forward_backward x := by rw [p.forward_backward, q.forward_backward]
def inverse (p : Perm) : Perm :=
  ⟨p.backward, p.forward, p.forward_backward, p.backward_forward⟩

def swap : Perm where
  forward | .zero => .one | .one => .zero | .two => .two
  backward | .zero => .one | .one => .zero | .two => .two
  backward_forward x := by cases x <;> rfl
  forward_backward x := by cases x <;> rfl

def cycle : Perm where
  forward | .zero => .one | .one => .two | .two => .zero
  backward | .zero => .two | .one => .zero | .two => .one
  backward_forward x := by cases x <;> rfl
  forward_backward x := by cases x <;> rfl

end Perm

/-- A finite product of symmetric groups, regarded as a one-object groupoid. -/
abbrev Action := Interface → Perm
def identityAction : Action := fun _ => Perm.identity
def thenAction (p q : Action) : Action := fun a => (p a).sequence (q a)
def inverseAction (p : Action) : Action := fun a => (p a).inverse

def mixed : Action
  | .A => Perm.swap
  | .B => Perm.cycle
  | .C => Perm.identity

def second : Action
  | .A => Perm.cycle
  | .B => Perm.swap
  | .C => Perm.swap

/-- Endpoint indices are retained even though all three carriers have size 3. -/
def Rel (_a _b : Interface) := Point → Point → Prop

def diagonal (a : Interface) : Rel a a := fun x y => x = y

def comp {a b c : Interface} (R : Rel a b) (S : Rel b c) : Rel a c :=
  fun x z => ∃ y, R x y ∧ S y z

def transportRel (p : Action) {a b : Interface} (R : Rel a b) : Rel a b :=
  fun x y => R ((p a).backward x) ((p b).backward y)

@[simp] theorem transportRel_identity {a b} (R : Rel a b) :
    transportRel identityAction R = R := rfl

@[simp] theorem transportRel_composite (p q : Action) {a b} (R : Rel a b) :
    transportRel q (transportRel p R) = transportRel (thenAction p q) R := rfl

theorem transportRel_inverse (p : Action) {a b} (R : Rel a b) :
    transportRel (inverseAction p) (transportRel p R) = R := by
  funext x y
  simp only [transportRel, inverseAction, Perm.inverse, Perm.backward_forward]

/-- The existential middle witness is transported, not erased or re-chosen. -/
theorem transportRel_comp (p : Action) {a b c} (R : Rel a b) (S : Rel b c) :
    transportRel p (comp R S) = comp (transportRel p R) (transportRel p S) := by
  funext x z
  apply propext
  constructor
  · intro h
    obtain ⟨y, hr, hs⟩ := h
    refine ⟨(p b).forward y, ?_, ?_⟩
    · simpa only [transportRel, Perm.backward_forward] using hr
    · simpa only [transportRel, Perm.backward_forward] using hs
  · intro h
    obtain ⟨y, hr, hs⟩ := h
    exact ⟨(p b).backward y, hr, hs⟩

theorem transportRel_diagonal (p : Action) (a : Interface) :
    transportRel p (diagonal a) = diagonal a := by
  funext x y
  apply propext
  constructor
  · intro h
    have hh := congrArg (p a).forward h
    simpa only [Perm.forward_backward, diagonal] using hh
  · intro h
    exact congrArg (p a).backward h

theorem comp_assoc {a b c d} (R : Rel a b) (S : Rel b c) (T : Rel c d) :
    comp (comp R S) T = comp R (comp S T) := by
  funext x w
  apply propext
  constructor
  · rintro ⟨z, ⟨y, hr, hs⟩, ht⟩
    exact ⟨y, hr, z, hs, ht⟩
  · rintro ⟨y, hr, z, hs, ht⟩
    exact ⟨z, ⟨y, hr, hs⟩, ht⟩

/-- Primitive binary witnesses retain a decoration in addition to exact validity. -/
structure Primitive (a b c : Interface) where
  left : Rel a b
  right : Rel b c
  output : Rel a c
  exactness : comp left right = output
  decoration : Bool

def transportPrimitive (p : Action) {a b c} (g : Primitive a b c) : Primitive a b c where
  left := transportRel p g.left
  right := transportRel p g.right
  output := transportRel p g.output
  exactness := (transportRel_comp p g.left g.right).symm.trans
    (congrArg (transportRel p) g.exactness)
  decoration := g.decoration

theorem transportPrimitive_identity {a b c} (g : Primitive a b c) :
    transportPrimitive identityAction g = g := by
  cases g
  rfl

theorem transportPrimitive_composite (p q : Action) {a b c} (g : Primitive a b c) :
    transportPrimitive q (transportPrimitive p g) = transportPrimitive (thenAction p q) g := rfl

theorem primitive_decoration_retained (p : Action) {a b c} (g : Primitive a b c) :
    (transportPrimitive p g).decoration = g.decoration := rfl

/-- Binary witnessed syntax; endpoints and every occurrence are retained. -/
inductive Expr : Interface → Interface → Type where
  | leaf {a b} (R : Rel a b) : Expr a b
  | unit (a) : Expr a a
  | binary {a b c} (decoration : Bool) (left : Expr a b) (right : Expr b c) : Expr a c

namespace Expr

def transport (p : Action) : {a b : Interface} → Expr a b → Expr a b
  | _, _, .leaf R => .leaf (transportRel p R)
  | _, _, .unit a => .unit a
  | _, _, .binary k l r => .binary k (transport p l) (transport p r)

@[simp] theorem transport_identity {a b} (t : Expr a b) :
    transport identityAction t = t := by
  induction t with
  | leaf R => rfl
  | unit a => rfl
  | binary k l r ihl ihr => simp only [transport, ihl, ihr]

theorem transport_composite (p q : Action) {a b} (t : Expr a b) :
    transport q (transport p t) = transport (thenAction p q) t := by
  induction t with
  | leaf R => rfl
  | unit a => rfl
  | binary k l r ihl ihr => simp only [transport, ihl, ihr]

theorem transport_inverse (p : Action) {a b} (t : Expr a b) :
    transport (inverseAction p) (transport p t) = t := by
  induction t with
  | leaf R => simp only [transport, transportRel_inverse]
  | unit a => rfl
  | binary k l r ihl ihr => simp only [transport, ihl, ihr]

def evaluate : {a b : Interface} → Expr a b → Rel a b
  | _, _, .leaf R => R
  | _, _, .unit a => diagonal a
  | _, _, .binary _ l r => comp (evaluate l) (evaluate r)

theorem evaluate_transport (p : Action) {a b} (t : Expr a b) :
    evaluate (transport p t) = transportRel p (evaluate t) := by
  induction t with
  | leaf R => rfl
  | unit a => exact (transportRel_diagonal p a).symm
  | binary k l r ihl ihr =>
    simp only [transport, evaluate, ihl, ihr, transportRel_comp]

/-- One slot for EACH leaf, including equal repeated component occurrences. -/
def Forest : {a b : Interface} → Expr a b → Type
  | _, _, .leaf R => { t : Expr _ _ // evaluate t = R }
  | _, _, .unit _ => Unit
  | _, _, .binary _ l r => Forest l × Forest r

def graft : {a b : Interface} → (t : Expr a b) → Forest t → Expr a b
  | _, _, .leaf _, f => f.val
  | _, _, .unit a, _ => .unit a
  | _, _, .binary k l r, f => .binary k (graft l f.1) (graft r f.2)

theorem evaluate_graft {a b} (t : Expr a b) (f : Forest t) :
    evaluate (graft t f) = evaluate t := by
  induction t with
  | leaf R => exact f.property
  | unit a => rfl
  | binary k l r ihl ihr =>
    simp only [graft, evaluate, ihl f.1, ihr f.2]

def transportForest (p : Action) : {a b : Interface} → (t : Expr a b) →
    Forest t → Forest (transport p t)
  | _, _, .leaf _, f => ⟨transport p f.val,
      (evaluate_transport p f.val).trans (congrArg (transportRel p) f.property)⟩
  | _, _, .unit _, _ => ()
  | _, _, .binary _ l r, f => (transportForest p l f.1, transportForest p r f.2)

/-- Exact witness-level endpoint law underlying the refinement comparison. -/
theorem transport_graft (p : Action) {a b} (t : Expr a b) (f : Forest t) :
    transport p (graft t f) = graft (transport p t) (transportForest p t f) := by
  induction t with
  | leaf R => rfl
  | unit a => rfl
  | binary k l r ihl ihr =>
    simp only [graft, transport, transportForest, ihl f.1, ihr f.2]

/-- A refinement arrow retains its full independent replacement forest. -/
structure Refinement {a b} (t u : Expr a b) where
  forest : Forest t
  target : graft t forest = u

def transportRefinement (p : Action) {a b} {t u : Expr a b}
    (f : Refinement t u) : Refinement (transport p t) (transport p u) where
  forest := transportForest p t f.forest
  target := (transport_graft p t f.forest).symm.trans (congrArg (transport p) f.target)

/-- Rotation family quantified over EVERY typed quadruple and both decorations. -/
inductive Equation : {a b : Interface} → Expr a b → Expr a b → Prop where
  | rotate {a b c d} (k l : Bool) (u : Expr a b) (v : Expr b c) (w : Expr c d) :
      Equation (.binary k (.binary l u v) w) (.binary l u (.binary k v w))

/-- Invariance is proved on declared generators, not postulated. -/
theorem equation_transport (p : Action) {a b} {t u : Expr a b}
    (h : Equation t u) : Equation (transport p t) (transport p u) := by
  cases h with
  | rotate k l u v w => exact Equation.rotate k l (transport p u) (transport p v) (transport p w)

theorem equation_evaluate {a b} {t u : Expr a b} (h : Equation t u) :
    evaluate t = evaluate u := by
  cases h with
  | rotate k l u v w => exact comp_assoc (evaluate u) (evaluate v) (evaluate w)

/-- Contextual equivalence closure. This is not a substitute for the full P theorem. -/
inductive Derives : {a b : Interface} → Expr a b → Expr a b → Prop where
  | equation {a b} {t u : Expr a b} : Equation t u → Derives t u
  | refl {a b} (t : Expr a b) : Derives t t
  | symm {a b} {t u : Expr a b} : Derives t u → Derives u t
  | trans {a b} {t u v : Expr a b} : Derives t u → Derives u v → Derives t v
  | binary {a b c} (k : Bool) {t u : Expr a b} {v w : Expr b c} :
      Derives t u → Derives v w → Derives (.binary k t v) (.binary k u w)

theorem derives_transport (p : Action) {a b} {t u : Expr a b}
    (h : Derives t u) : Derives (transport p t) (transport p u) := by
  induction h with
  | equation h => exact Derives.equation (equation_transport p h)
  | refl t => exact Derives.refl _
  | symm h ih => exact Derives.symm ih
  | trans h₁ h₂ ih₁ ih₂ => exact Derives.trans ih₁ ih₂
  | binary k h₁ h₂ ih₁ ih₂ => exact Derives.binary k ih₁ ih₂

def setoid (a b : Interface) : Setoid (Expr a b) where
  r := Derives
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

def presentedTransport (p : Action) {a b} : Quotient (setoid a b) → Quotient (setoid a b) :=
  Quotient.lift (fun t => Quotient.mk _ (transport p t))
    (fun _ _ h => Quotient.sound (derives_transport p h))

theorem presentedTransport_identity {a b} (x : Quotient (setoid a b)) :
    presentedTransport identityAction x = x := by
  refine Quotient.inductionOn x ?_
  intro t
  change Quotient.mk _ (transport identityAction t) = Quotient.mk _ t
  rw [transport_identity]

theorem presentedTransport_composite (p q : Action) {a b} (x : Quotient (setoid a b)) :
    presentedTransport q (presentedTransport p x) = presentedTransport (thenAction p q) x := by
  refine Quotient.inductionOn x ?_
  intro t
  change Quotient.mk _ (transport q (transport p t)) = Quotient.mk _ (transport (thenAction p q) t)
  rw [transport_composite]

end Expr

/-- A nontrivial transported relation with different source/target permutations. -/
def marked : Rel .A .B := fun x y => x = .zero ∧ y = .zero

theorem mixed_moves_marked : transportRel mixed marked .one .one := by
  constructor <;> rfl

theorem marked_not_at_image : ¬ marked .one .one := by
  intro h
  cases h.1

theorem composite_is_not_commutative :
    (thenAction mixed second .A).forward .zero ≠ (thenAction second mixed .A).forward .zero := by
  decide

/-- Both occurrences have exactly the same loop relation but independent forests. -/
def repeatRelation : Rel .A .A := fun _ _ => True
def repeated : Expr .A .A := Expr.binary false (.leaf repeatRelation) (.leaf repeatRelation)
def expanded : Expr .A .A := Expr.binary true (.leaf repeatRelation) (.leaf repeatRelation)

theorem expanded_evaluates : Expr.evaluate expanded = repeatRelation := by
  funext x z
  apply propext
  constructor
  · intro _; trivial
  · intro _; exact ⟨.zero, trivial, trivial⟩

def firstOnly : Expr.Forest repeated := (⟨expanded, expanded_evaluates⟩, ⟨.leaf repeatRelation, rfl⟩)
def secondOnly : Expr.Forest repeated := (⟨.leaf repeatRelation, rfl⟩, ⟨expanded, expanded_evaluates⟩)

theorem repeated_independent : Expr.graft repeated firstOnly ≠ Expr.graft repeated secondOnly := by
  intro h
  cases h

theorem repeated_independent_after_transport :
    Expr.transport mixed (Expr.graft repeated firstOnly) ≠
      Expr.transport mixed (Expr.graft repeated secondOnly) := by
  intro h
  have hi := congrArg (Expr.transport (inverseAction mixed)) h
  simp only [Expr.transport_inverse] at hi
  exact repeated_independent hi

/-! Explicit failure of quotient descent for a non-invariant primitive equation. -/
inductive Label where | alpha | beta | gamma
  deriving DecidableEq

def flipLabel : Label → Label
  | .alpha => .beta
  | .beta => .alpha
  | .gamma => .gamma

def betaCount : Label → Bool
  | .beta => true
  | _ => false

def badSetoid : Setoid Label where
  r x y := betaCount x = betaCount y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem bad_relation_not_invariant :
    badSetoid.r .alpha .gamma ∧ ¬ badSetoid.r (flipLabel .alpha) (flipLabel .gamma) := by
  constructor
  · rfl
  · change ¬ (true = false)
    decide

/-- Not merely a failed generator check: no function can induce this proposed map. -/
theorem bad_quotient_no_descent :
    ¬ ∃ F : Quotient badSetoid → Quotient badSetoid,
      ∀ x, F (Quotient.mk _ x) = Quotient.mk _ (flipLabel x) := by
  rintro ⟨F, hF⟩
  have original : (Quotient.mk badSetoid Label.alpha) = Quotient.mk badSetoid Label.gamma :=
    Quotient.sound (show betaCount .alpha = betaCount .gamma from rfl)
  have moved := congrArg F original
  rw [hF, hF] at moved
  have impossible := Quotient.exact moved
  exact bad_relation_not_invariant.2 impossible

/-- A nonidentity interface change fixes a nullary object; its witness is not trivial. -/
theorem mixed_nonidentity : mixed ≠ identityAction := by
  intro h
  have hh := congrArg (fun p : Action => (p .A).forward .zero) h
  cases hh

theorem unit_has_nontrivial_stabilizer :
    mixed ≠ identityAction ∧ Expr.transport mixed (Expr.unit .A) = Expr.unit .A :=
  ⟨mixed_nonidentity, rfl⟩

#print axioms transportPrimitive_identity
#print axioms transportPrimitive_composite
#print axioms bad_quotient_no_descent
#print axioms unit_has_nontrivial_stabilizer
#print axioms transportRel_comp
#print axioms Expr.transport_composite
#print axioms Expr.evaluate_transport
#print axioms Expr.transport_graft
#print axioms Expr.equation_transport
#print axioms Expr.derives_transport
#print axioms Expr.presentedTransport_composite
#print axioms Expr.transportRefinement
#print axioms repeated_independent_after_transport
end D1FiniteTypedAction
