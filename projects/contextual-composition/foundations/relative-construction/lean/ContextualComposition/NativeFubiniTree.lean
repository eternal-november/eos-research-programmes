module
public import ContextualComposition.NativeFubiniLeftUnit
@[expose] public section

/-! Arbitrary finite binary tensor trees, with leaves carrying the
original ragged dependent data and with genuine nullary subtrees.
The separate and joint operations are defined independently. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)

inductive DependentFubiniTree (I : C) where
  | unit
  | leaf (data : OrderedDependentAugData I)
  | fork (left right : DependentFubiniTree I)

namespace DependentFubiniTree

def jointInput : DependentFubiniTree I → OrderedDependentAugData I
  | .unit => OrderedDependentAugData.unit I
  | .leaf A => A
  | .fork l r => (jointInput l).product R L J (jointInput r)

noncomputable def separate : DependentFubiniTree I → Aug ℙ I
  | .unit => AugHom.unit I
  | .leaf A => A.accumulate R L J
  | .fork l r => independentAug R L (J.ρ I) (separate l) (separate r)

/-- The input maps have the same binary shape. At a leaf the presentation,
carrier, and actual whole fibre cells may vary arbitrarily. -/
inductive Map : DependentFubiniTree I → DependentFubiniTree I → Type _ where
  | unit : Map .unit .unit
  | leaf {A B : OrderedDependentAugData I} (f : OrderedDependentAugArrow A B) : Map (.leaf A) (.leaf B)
  | fork {a b c d : DependentFubiniTree I} (f : Map a b) (g : Map c d) : Map (.fork a c) (.fork b d)

noncomputable def Map.joint {a b : DependentFubiniTree I} (p : Map a b) :
    OrderedDependentAugArrow (a.jointInput R L J) (b.jointInput R L J) :=
  match p with
  | .unit => OrderedDependentAugArrow.ident _
  | .leaf f => f
  | .fork f g => (f.joint).product R L J N NR NL hl hr (g.joint)

noncomputable def Map.separate {a b : DependentFubiniTree I} (p : Map a b) :
    AugHom ℙ (a.separate R L J) (b.separate R L J) :=
  match p with
  | .unit => AugHom.ident _
  | .leaf f => f.accumulate R L J N NL hl
  | .fork f g => independentAugMap R L (J.ρ I) N NR NL hl hr (f.separate) (g.separate)

variable [IsIso (J.ρ I)]

/-- Actual Fubini for any chosen binary tree, including internal unit vertices. -/
noncomputable def comparison : (a : DependentFubiniTree I) →
    NativeAugmentedIso (a.separate R L J) ((a.jointInput R L J).accumulate R L J)
  | .unit => dependentUnitFubini R L hl hr J
  | .leaf A => NativeAugmentedIso.ident (A.accumulate R L J)
  | .fork a b =>
    let p := comparison a
    let q := comparison b
    (independentAugIso R L (J.ρ I) N NR NL hl hr p q).trans
      ((a.jointInput R L J).binaryFubini R L J N NR NL hl hr m mi h j unit_middle (b.jointInput R L J))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
theorem comparison_natural {a b : DependentFubiniTree I} (p : Map a b) :
    (p.separate R L J N NR NL hl hr).comp (b.comparison R L J N NR NL hl hr m mi h j unit_middle).hom =
      (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom.comp
        ((p.joint R L J N NR NL hl hr).accumulate R L J N NL hl) := by
  induction p with
  | unit =>
    simp only [Map.separate, Map.joint, comparison, AugHom.ident_comp,
      OrderedDependentAugArrow.accumulate_ident R L N NL hl hr J, AugHom.comp_ident]
  | leaf f =>
    simp only [Map.separate, Map.joint, comparison, NativeAugmentedIso.ident]
    exact (AugHom.comp_ident _).trans (AugHom.ident_comp _).symm
  | @fork a b c d f g fi gi =>
    let p₀ := f.separate R L J N NR NL hl hr
    let p₁ := g.separate R L J N NR NL hl hr
    let q₀ := f.joint R L J N NR NL hl hr
    let q₁ := g.joint R L J N NR NL hl hr
    let r₀ := q₀.accumulate R L J N NL hl
    let r₁ := q₁.accumulate R L J N NL hl
    let e₀ := (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom
    let e₁ := (c.comparison R L J N NR NL hl hr m mi h j unit_middle).hom
    let f₀ := (b.comparison R L J N NR NL hl hr m mi h j unit_middle).hom
    let f₁ := (d.comparison R L J N NR NL hl hr m mi h j unit_middle).hom
    let x := ((a.jointInput R L J).binaryFubini R L J N NR NL hl hr m mi h j unit_middle (c.jointInput R L J)).hom
    let y := ((b.jointInput R L J).binaryFubini R L J N NR NL hl hr m mi h j unit_middle (d.jointInput R L J)).hom
    let z := (q₀.product R L J N NR NL hl hr q₁).accumulate R L J N NL hl
    let H := fun {A B D E : Aug ℙ I} (p : AugHom ℙ A B) (q : AugHom ℙ D E) =>
      independentAugMap R L (J.ρ I) N NR NL hl hr p q
    change (H p₀ p₁).comp ((H f₀ f₁).comp y) = ((H e₀ e₁).comp x).comp z
    have s := independentAugMap_square R L (J.ρ I) N NR NL hl hr p₀ p₁ r₀ r₁ e₀ f₀ e₁ f₁ fi gi
    have t := OrderedDependentAugArrow.binaryFubini_natural R L J N NR NL hl hr m mi h j unit_middle q₀ q₁
    change (H r₀ r₁).comp y = x.comp z at t
    rw [← AugHom.comp_assoc, s, AugHom.comp_assoc, t, AugHom.comp_assoc]

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
