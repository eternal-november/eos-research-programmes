module
public import ContextualComposition.NativeIndependentSwapIso
@[expose] public section

/-! Actual binary Fubini and independent transposition, with exact
ordered preservation and both parent/continuation swaps on the joint side. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (P : TensorPrimitive T)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (Q : PrimitiveLinearity R L P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (ι : ∀ a b, IsIso (P.swap a b))
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable (A B : OrderedDependentAugData I)

local notation "ph" => binaryFubini R L J N NR NL hl hr m mi h j unit_middle
local notation "prd" => product R L J
local notation "acc" => accumulate R L J
local notation "fr" => accFrame R L J

set_option backward.isDefEq.respectTransparency false in
noncomputable def jointSwapComparison : ReadComparison (prd A B) (prd B A) where
  parent := independentSwapReadComparison R L P Q N A.V B.V A.xs B.xs J swap_unit ι A.ε B.ε
  child t := independentSwapReadComparison R L P Q N (A.A t.1) (B.A t.2) (A.us t.1) (B.us t.2) J swap_unit ι
    (A.δ t.1) (B.δ t.2)

noncomputable def jointSwap :=
  (jointSwapComparison R L J P N Q swap_unit ι A B).accumulate R L J NL hl

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateSwap :
    NativeAugmentedIso (independentAug R L (J.ρ I) (acc A) (acc B))
      (independentAug R L (J.ρ I) (acc B) (acc A)) :=
  independentSwapIso R L J P Q N swap_unit ι (dependentLabels (T:=T) A.V A.A) (dependentLabels (T:=T) B.V B.A)
    (dependentWord A.xs A.us) (dependentWord B.xs B.us) (accCell R L J A) (accCell R L J B)
    (dependentWord_nodup A.xs_unique A.us_unique) (dependentWord_nodup B.xs_unique B.us_unique)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5500000 in
/-- Binary Fubini commutes with the actual native independent swap.
The equation uses symmetric middle-four compatibility, not only the
underlying bijection of products. -/
theorem actual_fubini_swap (law : MedialSwap P m) :
    (ph A B).hom.comp (jointSwap R L J P N NL Q hl swap_unit ι A B).hom =
      (separateSwap R L J P N Q swap_unit ι A B).hom.comp (ph B A).hom := by
  let Ω := A.Branch × B.Branch
  let p := (ph A B).hom
  let q := (jointSwap R L J P N NL Q hl swap_unit ι A B).hom
  let r := (separateSwap R L J P N Q swap_unit ι A B).hom
  let s := (ph B A).hom
  let a (z : Ω) := A.V z.1.1
  let b (z : Ω) := A.A z.1.1 z.1.2
  let c (z : Ω) := B.V z.2.1
  let d (z : Ω) := B.A z.2.1 z.2.2
  let F (z : Ω) := T.obj (T.obj (a z) (b z)) (T.obj (c z) (d z))
  let G (z : Ω) := T.obj (T.obj (a z) (c z)) (T.obj (b z) (d z))
  let H (z : Ω) := T.obj (T.obj (c z) (d z)) (T.obj (a z) (b z))
  let K (z : Ω) := T.obj (T.obj (c z) (a z)) (T.obj (d z) (b z))
  let w₀ := (fr A).tensor T (fr B)
  let w₁ := jointFrame R L J A B
  let e := Equiv.prodComm B.Branch A.Branch
  let w₂ := ((fr B).tensor T (fr A)).relabel e e.injective H (fun _ => rfl)
  let w₃ := (jointFrame R L J B A).relabel e e.injective K (fun _ => rfl)
  let p₀ (z : Ω) : F z ⟶ G z := m.cell (a z) (b z) (c z) (d z)
  let q₀ (z : Ω) : G z ⟶ K z := T.map (P.swap (a z) (c z)) (P.swap (b z) (d z))
  let r₀ (z : Ω) : F z ⟶ H z := P.swap (T.obj (a z) (b z)) (T.obj (c z) (d z))
  let s₀ (z : Ω) : H z ⟶ K z := m.cell (c z) (d z) (a z) (b z)
  have hp : RawSingletonTrace w₀ w₁ p₀ p.native :=
    binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr A B
  have hq : RawSingletonTrace w₁ w₃ q₀ q.native := by
    let readIn := jointRead A B
    let readOut := (jointRead B A).trans e
    have h := ReadComparison.accumulate_trace R L J NL hl
      (jointSwapComparison R L J P N Q swap_unit ι A B) readIn readOut readIn.injective readOut.injective
      (fun _ => rfl) G K (fun _ => rfl) (fun _ => rfl) q₀ (fun _ => HEq.rfl)
    exact h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hr' : RawSingletonTrace w₀ w₂ r₀ r.native := by
    unfold r separateSwap
    exact independentSwapIso_trace R L J P Q N swap_unit ι _ _ _ _ _ _
      (dependentWord_nodup A.xs_unique A.us_unique) (dependentWord_nodup B.xs_unique B.us_unique)
  have hs : RawSingletonTrace w₂ w₃ s₀ s.native :=
    (binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr B A).relabel e e.injective
      H K (fun _ => rfl) (fun _ => rfl) s₀ (fun _ => HEq.rfl)
  apply AugHom.ext
  exact (hp.comp hq).eq (hr'.comp hs) (fun i =>
    law (a (w₃.read i)) (b (w₃.read i)) (c (w₃.read i)) (d (w₃.read i)))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData
