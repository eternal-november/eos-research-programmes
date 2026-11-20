import ContextualComposition.ContentActualBend
import ContextualComposition.ContentCorepresentableChart
import ContextualComposition.ContentComposition
import ContextualComposition.ContentCompositionCells
open CategoryTheory CategoryTheory.Functor Opposite
open ContextualComposition.GrothendieckStep
namespace ContentDirectedCovariant
set_option backward.isDefEq.respectTransparency false

inductive Token where | atom
instance : Category.{0} Token where
  Hom _ _ := Nat
  id _ := 0
  comp a b := a+b
  id_comp := by intros; apply Nat.zero_add
  comp_id := by intros; apply Nat.add_zero
  assoc := by intros; apply Nat.add_assoc

def P : Endpoints.{0,0,0,0} Natᵒᵖ where
  grades := (Functor.const _).obj (Cat.of Token)
  extend A := (Functor.const Token).obj A
  lift f := {app := fun _ => f}

def u : (0 : Nat) ⟶ 1 := homOfLE (by decide)
def v : (0 : Nat) ⟶ 2 := homOfLE (by decide)
def g : (1 : Nat) ⟶ 2 := homOfLE (by decide)
def x : ContentEndpointSquares.OldRow (P := P) 0 0 :=
  pair (RepresentableYoneda.rep (op 0)) (P.extend (op 0)) Token.atom (Discrete.mk (𝟙 _))
def y : ContentEndpointSquares.OldRow (P := P) 1 2 :=
  pair (RepresentableYoneda.rep (op 1)) (P.extend (op 2)) Token.atom (Discrete.mk g.op)
def beta (n : Nat) : RepresentableNativeEndpoints.Square v.op u.op y x :=
  ⟨show Token.atom ⟶ Token.atom from n, Subsingleton.elim _ _⟩
def read (n : Nat) := ContentEndpointSquares.compare u v x y (beta n)
theorem keepsDistinct : read 0 ≠ read 1 := by
  intro h
  exact Nat.zero_ne_one (congrArg Subtype.val ((ContentEndpointSquares.compare u v x y).injective h))
theorem noInverseLeg : ¬ Nonempty ((1 : Nat) ⟶ 0) :=
  fun ⟨h⟩ => (by decide : ¬ (1 : Nat) ≤ 0) (leOfHom h)

/-- A noninvertible payload 0→1 is accepted by the covariant integral.
The inverse orientation admits no arrow, even though the grade has many maps. -/
def payload : ContentCovariantGrothendieck.Dual (B := Nat) :=
  (Functor.const _).obj (Cat.of Natᵒᵖ)
def row0 : ContentCovariantGrothendieck.Row P payload 0 :=
  ContentCovariantGrothendieck.pair P payload (op Token.atom) (op (op 0))
def row1 : ContentCovariantGrothendieck.Row P payload 0 :=
  ContentCovariantGrothendieck.pair P payload (op Token.atom) (op (op 1))
def forward : row0 ⟶ row1 :=
  ContentCovariantGrothendieck.arrow P (Y := payload) (A := 0)
    (show op Token.atom ⟶ op Token.atom from (show Token.atom ⟶ Token.atom from (4 : Nat)).op) u.op.op

theorem forwardBody : forward.fiber = u.op.op := rfl
theorem noBackwardsPayload : ¬ Nonempty (row1 ⟶ row0) := fun ⟨h⟩ => noInverseLeg ⟨h.fiber.unop.unop⟩

noncomputable example {S : P.Split} (T : AmbientCoherentPseudomonad.Data S) :=
  ContentActualBend.bent T u v
noncomputable example {S : P.Split} (T : AmbientCoherentPseudomonad.Data S)
    (x : ContentComma.Native P 0 1) (y : ContentComma.Native P 1 2) :=
  ContentComposition.nativeFormula T x y
example := ContentCorepresentableChart.chart (0 : Nat)

end ContentDirectedCovariant
#print axioms ContentDirectedCovariant.keepsDistinct
#print axioms ContentDirectedCovariant.noBackwardsPayload
