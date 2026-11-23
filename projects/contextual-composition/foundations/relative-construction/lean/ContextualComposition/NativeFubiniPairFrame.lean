module
public import ContextualComposition.NativeDependentBothRetag
@[expose] public section

/-! Read the actual binary Fubini arrow by its two original branch
pairs, for reuse in independent and dependent regrouping diagrams. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

namespace OrderedDependentAugData

abbrev Branch (A : OrderedDependentAugData I) := A.X × A.U

noncomputable def accFrame (A : OrderedDependentAugData I) : RawSingletonFrame A.Branch (A.accumulate R L J).base :=
  rawWordFrame (dependentLabels (T:=T) A.V A.A) (dependentWord A.xs A.us)
    (dependentWord_nodup A.xs_unique A.us_unique)

def jointRead (A B : OrderedDependentAugData I) :
    ((A.X × B.X) × (A.U × B.U)) ≃ (A.Branch × B.Branch) where
  toFun t := ((t.1.1,t.2.1),(t.1.2,t.2.2))
  invFun t := ((t.1.1,t.2.1),(t.1.2,t.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def jointFrame (A B : OrderedDependentAugData I) :
    RawSingletonFrame (A.Branch × B.Branch) (((A.product R L J B).accumulate R L J).base) :=
  ((A.product R L J B).accFrame R L J).relabel (jointRead A B) (jointRead A B).injective
    (fun z => T.obj (T.obj (A.V z.1.1) (B.V z.2.1)) (T.obj (A.A z.1.1 z.1.2) (B.A z.2.1 z.2.2))) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
theorem binaryFubini_trace (A B : OrderedDependentAugData I) :
    RawSingletonTrace ((A.accFrame R L J).tensor T (B.accFrame R L J)) (A.jointFrame R L J B)
      (fun z => m.cell (A.V z.1.1) (A.A z.1.1 z.1.2) (B.V z.2.1) (B.A z.2.1 z.2.2))
      (A.binaryFubini R L J N NR NL hl hr m mi h j unit_middle B).hom.native := by
  let e : (A.Branch × B.Branch) ≃ (A.X × A.U × B.X × B.U) :=
    ⟨pairQuad, fun v => ((v.1,v.2.1),(v.2.2.1,v.2.2.2)), fun _ => rfl, fun _ => rfl⟩
  let F := (A.accFrame R L J).tensor T (B.accFrame R L J)
  let G := A.jointFrame R L J B
  let q := fun z : A.Branch × B.Branch =>
    m.cell (A.V z.1.1) (A.A z.1.1 z.1.2) (B.V z.2.1) (B.A z.2.1 z.2.2)
  have z := binaryProductAugIso_trace A.xs B.xs A.us B.us A.V B.V A.A B.A R L J A.δ B.δ A.ε B.ε
    N NR NL m mi h j unit_middle hl hr (dependentWord_nodup A.xs_unique A.us_unique)
    (dependentWord_nodup B.xs_unique B.us_unique)
    (dependentWord_nodup (A.product R L J B).xs_unique (A.product R L J B).us_unique)
    (occurrenceWord_nodup (dependentWord_nodup A.xs_unique A.us_unique) (dependentWord_nodup B.xs_unique B.us_unique))
  dsimp only at z
  have z' := z.relabel e.symm e.symm.injective F.label G.label (fun _ => rfl) (fun _ => rfl) q (fun _ => HEq.rfl)
  exact z'.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

end OrderedDependentAugData

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
