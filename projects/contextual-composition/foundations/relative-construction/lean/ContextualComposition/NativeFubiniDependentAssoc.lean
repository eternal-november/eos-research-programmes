module
public import ContextualComposition.NativeFubiniDependentAssocTrace
@[expose] public section

/-! The actual augmented Fubini comparison commutes with dependent
associativity on two independent three-level inputs. The parent and
tail Fubini whiskerings use their original different native orders. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentThirdData
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
set_option quotPrecheck false in
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C} {A B : OrderedDependentAugData I}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (P : TensorPrimitive T)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable (D : OrderedDependentThirdData A) (E : OrderedDependentThirdData B)

set_option quotPrecheck false in
local notation "ph" => OrderedDependentAugData.binaryFubini R L J N NR NL hl hr m mi h j unit_middle
set_option quotPrecheck false in
local notation "lft" => leftData R L J
set_option quotPrecheck false in
local notation "rgt" => rightData R L J
set_option quotPrecheck false in
local notation "prd" => OrderedDependentAugData.product R L J
set_option quotPrecheck false in
local notation "depAssoc" => fun D => associator R L J D P NL Q U hl ι
set_option quotPrecheck false in
local notation "timesIso" => independentAugIso R L (J.ρ I) N NR NL hl hr
set_option quotPrecheck false in
local notation "parentWhisk" => whiskerParentFubini R L J N NR NL m mi h j unit_middle hl hr D E
set_option quotPrecheck false in
local notation "tailWhisk" => whiskerTailFubini R L J N NR NL m mi h j unit_middle hl hr D E
set_option quotPrecheck false in
local notation "joint" => product R L J D E

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 8500000 in
/-- For two independent factors at three dependent levels, the two
literal native Fubini paths commute with dependent reassociation.
No rectangularity of the individual continuation words is assumed. -/
theorem actual_fubini_dependent_assoc (law : MedialDependentAssoc P m) :
    (((ph (lft D) (lft E)).hom.comp (parentWhisk).hom).comp ((depAssoc) joint).hom) =
      ((((timesIso ((depAssoc) D) ((depAssoc) E)).hom).comp (ph (rgt D) (rgt E)).hom).comp (tailWhisk).hom) := by
  let Ω := RightBranch D × RightBranch E
  let p := (ph (lft D) (lft E)).hom
  let q := (parentWhisk).hom
  let r := ((depAssoc) joint).hom
  let s := (timesIso ((depAssoc) D) ((depAssoc) E)).hom
  let t := (ph (rgt D) (rgt E)).hom
  let u := (tailWhisk).hom
  let a (z : Ω) := A.V z.1.1
  let b (z : Ω) := A.A z.1.1 z.1.2.1
  let c (z : Ω) := D.D z.1.1 z.1.2.1 z.1.2.2
  let d (z : Ω) := B.V z.2.1
  let e (z : Ω) := B.A z.2.1 z.2.2.1
  let f (z : Ω) := E.D z.2.1 z.2.2.1 z.2.2.2
  let F₀ (z : Ω) := T.obj (T.obj (T.obj (a z) (b z)) (c z)) (T.obj (T.obj (d z) (e z)) (f z))
  let F₁ (z : Ω) := T.obj (T.obj (T.obj (a z) (b z)) (T.obj (d z) (e z))) (T.obj (c z) (f z))
  let F₂ (z : Ω) := T.obj (T.obj (T.obj (a z) (d z)) (T.obj (b z) (e z))) (T.obj (c z) (f z))
  let F₃ (z : Ω) := T.obj (T.obj (a z) (d z)) (T.obj (T.obj (b z) (e z)) (T.obj (c z) (f z)))
  let F₄ (z : Ω) := T.obj (T.obj (a z) (T.obj (b z) (c z))) (T.obj (d z) (T.obj (e z) (f z)))
  let F₅ (z : Ω) := T.obj (T.obj (a z) (d z)) (T.obj (T.obj (b z) (c z)) (T.obj (e z) (f z)))
  let left := (leftDataRead R L J D).prodCongr (leftDataRead R L J E)
  let lread := leftPairRead R L J D E
  let rread := rightPairRead R L J D E
  let t₁ := (OrderedDependentAugData.jointRead (lft D) (lft E)).trans left
  let t₅ := OrderedDependentAugData.jointRead (rgt D) (rgt E)
  let w₀ := (leftDataFrame R L J D).tensor T (leftDataFrame R L J E)
  let w₁ := ((prd (lft D) (lft E)).accFrame R L J).relabel t₁ t₁.injective F₁ (fun _ => rfl)
  let w₂ := ((lft joint).accFrame R L J).relabel lread lread.injective F₂ (fun _ => rfl)
  let w₃ := ((rgt joint).accFrame R L J).relabel rread rread.injective F₃ (fun _ => rfl)
  let w₄ := (rightDataFrame R L J D).tensor T (rightDataFrame R L J E)
  let w₅ := ((prd (rgt D) (rgt E)).accFrame R L J).relabel t₅ t₅.injective F₅ (fun _ => rfl)
  let p₀ (z : Ω) : F₀ z ⟶ F₁ z := m.cell (T.obj (a z) (b z)) (c z) (T.obj (d z) (e z)) (f z)
  let q₀ (z : Ω) : F₁ z ⟶ F₂ z := T.map (m.cell (a z) (b z) (d z) (e z)) (𝟙 (T.obj (c z) (f z)))
  let r₀ (z : Ω) : F₂ z ⟶ F₃ z := P.assoc (T.obj (a z) (d z)) (T.obj (b z) (e z)) (T.obj (c z) (f z))
  let s₀ (z : Ω) : F₀ z ⟶ F₄ z := T.map (P.assoc (a z) (b z) (c z)) (P.assoc (d z) (e z) (f z))
  let t₀ (z : Ω) : F₄ z ⟶ F₅ z := m.cell (a z) (T.obj (b z) (c z)) (d z) (T.obj (e z) (f z))
  let u₀ (z : Ω) : F₅ z ⟶ F₃ z := T.map (𝟙 (T.obj (a z) (d z))) (m.cell (b z) (c z) (e z) (f z))
  have hp : RawSingletonTrace w₀ w₁ p₀ p.native := by
    have a := (OrderedDependentAugData.binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr (lft D) (lft E)).relabel
      left left.injective F₀ F₁ (fun _ => rfl) (fun _ => rfl) p₀ (fun _ => HEq.rfl)
    exact a.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hq : RawSingletonTrace w₁ w₂ q₀ q.native := by
    unfold q whiskerParentFubini
    exact OrderedDependentAugData.ReadComparison.accumulate_trace R L J NL hl
      (parentFubiniComparison R L J N NR NL m mi h j unit_middle hl hr D E)
      t₁ lread t₁.injective lread.injective (fun _ => rfl) F₁ F₂ (fun _ => rfl) (fun _ => rfl)
      q₀ (fun _ => HEq.rfl)
  have hr' : RawSingletonTrace w₂ w₃ r₀ r.native := by
    have a := (associator_trace R L J joint P NL Q U hl ι).relabel
      rread rread.injective F₂ F₃ (fun _ => rfl) (fun _ => rfl) r₀ (fun _ => HEq.rfl)
    exact a.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hs : RawSingletonTrace w₀ w₄ s₀ s.native :=
    (associator_trace R L J D P NL Q U hl ι).tensor R L hl hr (associator_trace R L J E P NL Q U hl ι)
  have ht : RawSingletonTrace w₄ w₅ t₀ t.native :=
    OrderedDependentAugData.binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr (rgt D) (rgt E)
  have hu : RawSingletonTrace w₅ w₃ u₀ u.native := by
    unfold u whiskerTailFubini
    exact OrderedDependentAugData.ReadComparison.accumulate_trace R L J NL hl
      (tailFubiniComparison R L J N NR NL m mi h j unit_middle hl hr D E)
      t₅ rread t₅.injective rread.injective (fun _ => rfl) F₅ F₃ (fun _ => rfl) (fun _ => rfl)
      u₀ (fun _ => HEq.rfl)
  apply AugHom.ext
  change (p.native.comp q.native).comp r.native = (s.native.comp t.native).comp u.native
  exact ((hp.comp hq).comp hr').eq ((hs.comp ht).comp hu) (fun i => by
    simp only [Category.assoc]
    exact law (a (w₃.read i)) (b (w₃.read i)) (c (w₃.read i))
      (d (w₃.read i)) (e (w₃.read i)) (f (w₃.read i)))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentThirdData
