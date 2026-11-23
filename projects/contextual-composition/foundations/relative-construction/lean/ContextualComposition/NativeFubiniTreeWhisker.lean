module
public import ContextualComposition.NativeFubiniReadNaturality
@[expose] public section

/-! Whisker a proved Fubini coherence square through any encompassing
binary tensor node. Both resulting structural arrows are literal. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
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
variable [IsIso (J.ρ I)]
local notation "ph" => comparison R L J N NR NL hl hr m mi h j unit_middle
local notation "sep" => separate R L J
local notation "inp" => jointInput R L J
local notation "nm" => independentAugMap R L (J.ρ I) N NR NL hl hr
local notation "rc" => OrderedDependentAugData.ReadComparison.accumulate R L J NL hl
local notation "rp" => OrderedDependentAugData.ReadComparison.product R L J NR NL hl hr

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4800000 in
/-- A product of subtrees whose structural squares commute has the
commuting square for the actual separately formed tensor and joint read. -/
theorem comparison_fork_congr {a b c d : DependentFubiniTree I}
    (e : AugHom ℙ (separate R L J a) (separate R L J b))
    (f : AugHom ℙ (separate R L J c) (separate R L J d))
    (p : OrderedDependentAugData.ReadComparison (jointInput R L J a) (jointInput R L J b))
    (q : OrderedDependentAugData.ReadComparison (jointInput R L J c) (jointInput R L J d))
    (he : e.comp (ph b).hom = (ph a).hom.comp (rc p).hom)
    (hf : f.comp (ph d).hom = (ph c).hom.comp (rc q).hom) :
    (nm e f).comp (ph (.fork b d)).hom = (ph (.fork a c)).hom.comp (rc (rp p q)).hom := by
  let ax := inp a
  let bx := inp b
  let cx := inp c
  let dx := inp d
  let x := (ax.binaryFubini R L J N NR NL hl hr m mi h j unit_middle cx).hom
  let y := (bx.binaryFubini R L J N NR NL hl hr m mi h j unit_middle dx).hom
  let v := (rc (rp p q)).hom
  have h₁ := independentAugMap_square R L (J.ρ I) N NR NL hl hr
    e f (rc p).hom (rc q).hom (ph a).hom (ph b).hom (ph c).hom (ph d).hom he hf
  have h₂ := OrderedDependentAugData.ReadComparison.binaryFubini_natural R L J N NR NL hl hr
    m mi h j unit_middle p q
  change (nm e f).comp ((nm (ph b).hom (ph d).hom).comp y) =
    ((nm (ph a).hom (ph c).hom).comp x).comp v
  change (nm (rc p).hom (rc q).hom).comp y = x.comp v at h₂
  rw [← AugHom.comp_assoc, h₁, AugHom.comp_assoc, h₂, AugHom.comp_assoc]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
