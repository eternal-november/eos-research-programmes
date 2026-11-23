module
public import ContextualComposition.NativeIndependentAssocTrace
@[expose] public section

/-! Associative independent regrouping of the actual augmented Fubini
comparison. Both paths are literal native composites, compared at
matching raw branch triples rather than by carrier faithfulness. -/
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
variable (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable (A B D : OrderedDependentAugData I)
local notation "acc" => accumulate R L J
local notation "prd" => product R L J
local notation "ph" => binaryFubini R L J N NR NL hl hr m mi h j unit_middle
local notation "fr" => accFrame R L J
set_option quotPrecheck false in
local notation "timesIso" => independentAugIso R L (J.ρ I) N NR NL hl hr
local notation "reg" => jointRegroup R L J P NR NL Q U hl hr ι

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateRegroup :
    NativeAugmentedIso
      (independentAug R L (J.ρ I) (independentAug R L (J.ρ I) (acc A) (acc B)) (acc D))
      (independentAug R L (J.ρ I) (acc A) (independentAug R L (J.ρ I) (acc B) (acc D))) :=
  independentAssocIso R L J P NR NL Q U (dependentLabels (T:=T) A.V A.A) (dependentLabels (T:=T) B.V B.A)
    (dependentLabels (T:=T) D.V D.A)
    (dependentWord A.xs A.us) (dependentWord B.xs B.us) (dependentWord D.xs D.us)
    (dependentWordAugCell R L J A.xs A.us A.V A.A (indexedAugmentation A.δ) A.ε)
    (dependentWordAugCell R L J B.xs B.us B.V B.A (indexedAugmentation B.δ) B.ε)
    (dependentWordAugCell R L J D.xs D.us D.V D.A (indexedAugmentation D.δ) D.ε)
    hl hr ι (nodup_product_word (dependentWord_nodup A.xs_unique A.us_unique)
      (nodup_product_word (dependentWord_nodup B.xs_unique B.us_unique)
        (dependentWord_nodup D.xs_unique D.us_unique)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 8000000 in
/-- The two actual bracketings of ternary independent Fubini agree,
after independent reassociation on the separate side and the
parent/continuation regroupings on the joint side. -/
theorem actual_fubini_regrouping (law : MedialRegroup P m) :
    (((timesIso (ph A B) (NativeAugmentedIso.ident (acc D))).hom.comp
          (ph (prd A B) D).hom).comp (reg A B D).hom) =
      (((separateRegroup R L J P NR NL Q U hl hr ι A B D).hom.comp
          (timesIso (NativeAugmentedIso.ident (acc A)) (ph B D)).hom).comp
          (ph A (prd B D)).hom) := by
  let X := fr A
  let Y := fr B
  let Z := fr D
  let Ω := TripleBranch A B D
  let p := (timesIso (ph A B) (NativeAugmentedIso.ident (acc D))).hom
  let q := (ph (prd A B) D).hom
  let r := (reg A B D).hom
  let s := (separateRegroup R L J P NR NL Q U hl hr ι A B D).hom
  let t := (timesIso (NativeAugmentedIso.ident (acc A)) (ph B D)).hom
  let u := (ph A (prd B D)).hom
  let a₁ (z : Ω) := A.V z.1.1
  let a₂ (z : Ω) := A.A z.1.1 z.1.2
  let b₁ (z : Ω) := B.V z.2.1.1
  let b₂ (z : Ω) := B.A z.2.1.1 z.2.1.2
  let d₁ (z : Ω) := D.V z.2.2.1
  let d₂ (z : Ω) := D.A z.2.2.1 z.2.2.2
  let F₀ (z : Ω) := T.obj (T.obj (T.obj (a₁ z) (a₂ z)) (T.obj (b₁ z) (b₂ z))) (T.obj (d₁ z) (d₂ z))
  let F₁ (z : Ω) := T.obj (T.obj (T.obj (a₁ z) (b₁ z)) (T.obj (a₂ z) (b₂ z))) (T.obj (d₁ z) (d₂ z))
  let F₂ := groupedLeftLabel (T:=T) A B D
  let F₃ := groupedRightLabel (T:=T) A B D
  let F₄ (z : Ω) := T.obj (T.obj (a₁ z) (a₂ z)) (T.obj (T.obj (b₁ z) (b₂ z)) (T.obj (d₁ z) (d₂ z)))
  let F₅ (z : Ω) := T.obj (T.obj (a₁ z) (a₂ z)) (T.obj (T.obj (b₁ z) (d₁ z)) (T.obj (b₂ z) (d₂ z)))
  let w₀ := (((X.tensor T Y).tensor T Z).relabel tripleRetag tripleRetag.injective F₀ (fun _ => rfl))
  let w₁ := (((jointFrame R L J A B).tensor T Z).relabel tripleRetag tripleRetag.injective F₁ (fun _ => rfl))
  let w₂ := groupedLeftFrame R L J A B D
  let w₃ := groupedRightFrame R L J A B D
  let w₄ := X.tensor T (Y.tensor T Z)
  let w₅ := X.tensor T (jointFrame R L J B D)
  let p₀ (z : Ω) : F₀ z ⟶ F₁ z := T.map (m.cell (a₁ z) (a₂ z) (b₁ z) (b₂ z)) (𝟙 (T.obj (d₁ z) (d₂ z)))
  let q₀ (z : Ω) : F₁ z ⟶ F₂ z := m.cell (T.obj (a₁ z) (b₁ z)) (T.obj (a₂ z) (b₂ z)) (d₁ z) (d₂ z)
  let r₀ (z : Ω) : F₂ z ⟶ F₃ z := T.map (P.assoc (a₁ z) (b₁ z) (d₁ z)) (P.assoc (a₂ z) (b₂ z) (d₂ z))
  let s₀ (z : Ω) : F₀ z ⟶ F₄ z := P.assoc (T.obj (a₁ z) (a₂ z)) (T.obj (b₁ z) (b₂ z)) (T.obj (d₁ z) (d₂ z))
  let t₀ (z : Ω) : F₄ z ⟶ F₅ z := T.map (𝟙 (T.obj (a₁ z) (a₂ z))) (m.cell (b₁ z) (b₂ z) (d₁ z) (d₂ z))
  let u₀ (z : Ω) : F₅ z ⟶ F₃ z := m.cell (a₁ z) (a₂ z) (T.obj (b₁ z) (d₁ z)) (T.obj (b₂ z) (d₂ z))
  have pT := binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr A B
  have tT := binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr B D
  have hp : RawSingletonTrace w₀ w₁ p₀ p.native :=
    (pT.tensor R L hl hr (RawSingletonTrace.ident Z)).relabel tripleRetag tripleRetag.injective F₀ F₁
      (fun _ => rfl) (fun _ => rfl) p₀ (fun _ => HEq.rfl)
  have ht : RawSingletonTrace w₄ w₅ t₀ t.native := (RawSingletonTrace.ident X).tensor R L hl hr tT
  have hq : RawSingletonTrace w₁ w₂ q₀ q.native := by
    let f : (prd A B).Branch × D.Branch ≃ Ω := ((jointRead A B).prodCongr (Equiv.refl D.Branch)).trans tripleRetag
    have a := (binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr (prd A B) D).relabel
      f f.injective F₁ F₂ (fun _ => rfl) (fun _ => rfl) q₀ (fun _ => HEq.rfl)
    exact a.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hu : RawSingletonTrace w₅ w₃ u₀ u.native := by
    let f : A.Branch × (prd B D).Branch ≃ Ω := (Equiv.refl A.Branch).prodCongr (jointRead B D)
    have a := (binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr A (prd B D)).relabel
      f f.injective F₅ F₃ (fun _ => rfl) (fun _ => rfl) u₀ (fun _ => HEq.rfl)
    exact a.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hr' : RawSingletonTrace w₂ w₃ r₀ r.native := jointRegroup_trace R L J P NR NL Q U hl hr ι A B D
  have hs : RawSingletonTrace w₀ w₄ s₀ s.native := by
    unfold s separateRegroup
    exact independentAssocIso_trace R L J P NR NL Q U hl hr ι _ _ _ _ _ _ _ _ _
      (dependentWord_nodup A.xs_unique A.us_unique)
      (dependentWord_nodup B.xs_unique B.us_unique)
      (dependentWord_nodup D.xs_unique D.us_unique)
  apply AugHom.ext
  change (p.native.comp q.native).comp r.native = (s.native.comp t.native).comp u.native
  exact ((hp.comp hq).comp hr').eq ((hs.comp ht).comp hu) (fun i => by
    simp only [Category.assoc]
    exact law (a₁ (w₃.read i)) (a₂ (w₃.read i)) (b₁ (w₃.read i))
      (b₂ (w₃.read i)) (d₁ (w₃.read i)) (d₂ (w₃.read i)))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData
