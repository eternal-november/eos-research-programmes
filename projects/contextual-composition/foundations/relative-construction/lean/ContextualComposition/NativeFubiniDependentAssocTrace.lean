module
public import ContextualComposition.NativeFubiniDependentWhiskers
@[expose] public section

/-! Exact triple and paired-triple native frames for the dependent
associativity coherence of Fubini. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentThirdData
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C} {A B : OrderedDependentAugData I}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (D : OrderedDependentThirdData A) (E : OrderedDependentThirdData B)
local notation "leftD" => leftData R L J D
local notation "leftE" => leftData R L J E
local notation "rightD" => rightData R L J D
local notation "rightE" => rightData R L J E
local notation "joint" => product R L J D E
local notation "prd" => OrderedDependentAugData.product R L J
local notation "acc" => OrderedDependentAugData.accumulate R L J

abbrev RightBranch (D : OrderedDependentThirdData A) := A.X × A.U × D.W
local notation "Ω" => (RightBranch D × RightBranch E)

def leftDataRead : (leftD).Branch ≃ RightBranch D := tripleRetag

noncomputable def leftDataFrame :
    RawSingletonFrame (RightBranch D) (acc leftD).base :=
  let f := leftDataRead R L J D
  ((leftD).accFrame R L J).relabel f f.injective (assocLeftLabels T A.V A.A D.D ∘ f.symm) (fun _ => rfl)

noncomputable def rightDataFrame :
    RawSingletonFrame (RightBranch D) (acc rightD).base :=
  (rightD).accFrame R L J

variable (P : TensorPrimitive T) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] (hl : ∀ a : C, SameLeftGather T a L)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))

set_option backward.isDefEq.respectTransparency false in
theorem associator_trace :
    RawSingletonTrace (leftDataFrame R L J D) (rightDataFrame R L J D)
      (fun z => P.assoc (A.V z.1) (A.A z.1 z.2.1) (D.D z.1 z.2.1 z.2.2))
      (associator R L J D P NL Q U hl ι).hom.native := by
  let f := leftDataRead R L J D
  let s := dependentWord (leftD).xs (leftD).us
  let t := dependentWord (rightD).xs (rightD).us
  let hn := dependentWord_nodup (rightD).xs_unique (rightD).us_unique
  let G := assocLeftLabels T A.V A.A D.D ∘ f.symm
  let H := assocRightLabels T A.V A.A D.D
  let p : ∀ z, G z ⟶ H z := fun z => P.assoc (A.V z.1) (A.A z.1 z.2.1) (D.D z.1 z.2.1 z.2.2)
  let h := tripleRetag_word A.xs A.us D.ws
  let e := wordFamily_read_eq G f s t h
  have hg (i : Fin _) : (leftDataFrame R L J D).read i =
      (rawWordFrame G t hn).read (Fin.cast (congrArg Family.n e) i) :=
    rawWordFrame_read_cast G f s t h i
  have k := dependentAssocIso_pointwise_heq R L J P NL Q U hl A.xs A.us D.ws A.V A.A D.D A.ε A.δ D.γ ι hn
  exact (wordPointwise_trace t hn p).retarget e.symm rfl k.symm
    (rawFrame_read_reverse (leftDataFrame R L J D) (rawWordFrame G t hn) e hg) (fun _ => rfl) (fun _ => HEq.rfl)

def leftPairRead : ((leftData R L J joint).Branch) ≃ Ω where
  toFun t := ((t.1.1.1,t.1.2.1,t.2.1),(t.1.1.2,t.1.2.2,t.2.2))
  invFun z := (((z.1.1,z.2.1),(z.1.2.1,z.2.2.1)),(z.1.2.2,z.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rightPairRead : ((rightData R L J joint).Branch) ≃ Ω where
  toFun t := ((t.1.1,t.2.1.1,t.2.2.1),(t.1.2,t.2.1.2,t.2.2.2))
  invFun z := ((z.1.1,z.2.1),((z.1.2.1,z.2.2.1),(z.1.2.2,z.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentThirdData
