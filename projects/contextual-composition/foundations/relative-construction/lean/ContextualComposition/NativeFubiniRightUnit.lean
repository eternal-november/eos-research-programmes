module
public import ContextualComposition.NativeIndependentRightUnit
public import ContextualComposition.NativeFubiniSwap
@[expose] public section

/-! Literal binary Fubini against the nullary independent comparison.
The two paths are compared towards the unchanged augmented accumulation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v

section Law
variable {C : Type u} [cat : Category.{v} C]
def MedialRightUnit {T : Bi (coeff (C:=C))} {S : Bi (coeff (C:=C))} {Z I : C}
    (R : Gather S T Z) (J : UnitCompat R I) (m : Middle T I) : Prop :=
  ∀ a b, m.cell a b I I ≫ T.map (J.ρ a) (J.ρ b) = T.map (𝟙 (T.obj a b)) (J.ρ I) ≫ J.ρ (T.obj a b)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem standardMedialRightUnit (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul)
    {S : Bi (coeff (C:=C))} {Z : C}
    (r : Gather S (binary (@Binary.ofMonoidal C cat mul)) Z)
    (j : UnitCompat r (@MonoidalCategoryStruct.tensorUnit C cat mul.toMonoidalCategoryStruct))
    (h : ∀ a : C, j.ρ a = (@MonoidalCategoryStruct.rightUnitor C cat mul.toMonoidalCategoryStruct a).hom) :
    MedialRightUnit r j (additiveMiddle (@Additive.ofBraided C cat mul br)) := by
  intro a b
  letI := mul
  letI := br
  simp only [h]
  change tensorμ a b (𝟙_ C) (𝟙_ C) ≫ ((ρ_ a).hom ⊗ₘ (ρ_ b).hom) =
    (𝟙 (a ⊗ b) ⊗ₘ (ρ_ (𝟙_ C)).hom) ≫ (ρ_ (a ⊗ b)).hom
  rw [id_tensorHom]
  have hh : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by monoidal_coherence
  rw [hh]
  apply (cancel_epi ((a ⊗ b) ◁ (λ_ (𝟙_ C)).inv)).mp
  simpa only [← Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp] using
    (tensor_right_unitality a b).symm

end Law

namespace OrderedDependentAugData
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (iρ : ∀ a, IsIso (J.ρ a))
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable (A : OrderedDependentAugData I)

local notation "ph" => binaryFubini R L J N NR NL hl hr m mi h j unit_middle
local notation "prd" => product R L J
local notation "acc" => accumulate R L J
local notation "fr" => accFrame R L J
local notation "U" => OrderedDependentAugData.unit I

set_option backward.isDefEq.respectTransparency false in
noncomputable def jointRightUnitComparison : ReadComparison (prd A U) A where
  parent := independentRightUnit_read R L J A.V A.xs A.ε (hl:=hl) (iρ:=iρ)
  child t := independentRightUnit_read R L J (A.A t.1) (A.us t.1) (A.δ t.1) (hl:=hl) (iρ:=iρ)

noncomputable def jointRightUnit :=
  (jointRightUnitComparison R L J hl iρ A).accumulate R L J NL hl

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateRightUnit :
    NativeAugmentedIso (independentAug R L (J.ρ I) (acc A) (AugHom.unit (S:=ℙ) I)) (acc A) :=
  independentRightUnitIso R L J (dependentLabels (T:=T) A.V A.A) (dependentWord A.xs A.us)
    (accCell R L J A) hl iρ (dependentWord_nodup A.xs_unique A.us_unique)

theorem nullaryBranch_eq (a b : (OrderedDependentAugData.unit I).Branch) : a = b :=
  @Subsingleton.elim (PUnit.{u+1} × PUnit.{u+1}) inferInstance a b

/-- Re-index the actual nullary dependent carrier as one independent unit address. -/
noncomputable def nullaryFrame :=
  (fr U).relabel (fun _ => (PUnit.unit : PUnit.{u+1}))
    (fun a b _ => nullaryBranch_eq a b) (fun _ => T.obj I I) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
theorem dependentUnitFubini_inv_trace [IsIso (J.ρ I)] :
    let G : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
      rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
    RawSingletonTrace (nullaryFrame R L J) G (fun _ => J.ρ I)
      (dependentUnitFubini R L hl hr J).inv.native := by
  intro G
  let F := nullaryFrame R L J
  let e : Fin (acc U).base.n ≃ Fin 1 := Equiv.refl (Fin 1)
  let s := fun _ : Fin 1 => J.ρ I
  have he : (dependentUnitFubini R L hl hr J).inv.native = nativeSingletonMap e s := by
    have E : (dependentUnitFubini R L hl hr J).inv.native = (acc U).ε :=
      congrArg AugHom.native (AugHom.terminal (dependentUnitFubini R L hl hr J).inv)
    rw [E]
    apply native_hom_eq_of_cell_heq
    · funext i
      change (_ : Fin 1) = (_ : Fin 1)
      exact Subsingleton.elim _ _
    · intro k
      have q := nativeSingletonMap_cell_heq e s k
      have cell : HEq (eqToHom (wordFoldPin (fun _ : PUnit.{u+1} × PUnit.{u+1} => T.obj I I)
          [(PUnit.unit,PUnit.unit)] k) ≫
            dependentWordAugCell R L J [PUnit.unit]
              (fun _ : PUnit.{u+1} => [PUnit.unit]) (fun _ => I) (fun _ _ => I)
              (indexedAugmentation (fun _ => (ρ_ I).hom)) (ρ_ I).hom)
          ((ρ_ (T.obj I I)).hom ≫ J.ρ I) := by
        rw [dependentUnit_augCell R L hl hr J]
        have t : HEq (eqToHom (wordFoldPin (fun _ : PUnit.{u+1} × PUnit.{u+1} => T.obj I I)
            [(PUnit.unit,PUnit.unit)] k) ≫ (ρ_ (T.obj I I)).hom ≫ J.ρ I)
            ((ρ_ (T.obj I I)).hom ≫ J.ρ I) := hom_source_pin_heq _ _
        exact t
      exact cell.trans q.symm
  exact ⟨e,s,he,fun _ => Subsingleton.elim _ _,fun _ => HEq.rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5500000 in
/-- Using the inverse nullary comparison makes both paths start at the
actual independent product of two accumulations. -/
theorem actual_fubini_right_unit [IsIso (J.ρ I)] (law : MedialRightUnit R J m) :
    (ph A U).hom.comp (jointRightUnit R L J NL hl iρ A).hom =
      (independentAugMap R L (J.ρ I) N NR NL hl hr (AugHom.ident (acc A))
        (dependentUnitFubini R L hl hr J).inv).comp (separateRightUnit R L J hl iρ A).hom := by
  let e := dependentUnitFubini R L hl hr J
  let p := (ph A U).hom
  let q := (jointRightUnit R L J NL hl iρ A).hom
  let r := independentAugMap R L (J.ρ I) N NR NL hl hr (AugHom.ident (acc A)) e.inv
  let s := (separateRightUnit R L J hl iρ A).hom
  let Ω := A.Branch × PUnit.{u+1}
  let a (z : Ω) := A.V z.1.1
  let b (z : Ω) := A.A z.1.1 z.1.2
  let V (z : Ω) := T.obj (a z) (b z)
  let F (z : Ω) := T.obj (V z) (T.obj I I)
  let G (z : Ω) := T.obj (T.obj (a z) I) (T.obj (b z) I)
  let H (z : Ω) := T.obj (V z) I
  let f : A.Branch × (U).Branch → Ω := fun z => (z.1,PUnit.unit)
  have fi : Function.Injective f := fun _ _ eq => Prod.ext (congrArg (fun z : Ω => z.1) eq) (nullaryBranch_eq _ _)
  let u : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
    rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
  let v := fun x : A.Branch => ((x,PUnit.unit) : Ω)
  have vi : Function.Injective v := fun _ _ h => congrArg Prod.fst h
  let w₀ := (fr A).tensor T (nullaryFrame R L J)
  let w₁ := (jointFrame R L J A U).relabel f fi G (fun _ => rfl)
  let w₂ := (fr A).tensor T u
  let w₃ := (fr A).relabel v vi V (fun _ => rfl)
  let p₀ (z : Ω) : F z ⟶ G z := m.cell (a z) (b z) I I
  let q₀ (z : Ω) : G z ⟶ V z := T.map (J.ρ (a z)) (J.ρ (b z))
  let r₀ (z : Ω) : F z ⟶ H z := T.map (𝟙 (V z)) (J.ρ I)
  let s₀ (z : Ω) : H z ⟶ V z := J.ρ (V z)
  have hp : RawSingletonTrace w₀ w₁ p₀ p.native := by
    have u := (binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr A U).relabel
      f fi F G (fun _ => rfl) (fun _ => rfl) p₀ (fun _ => HEq.rfl)
    exact u.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hq : RawSingletonTrace w₁ w₃ q₀ q.native := by
    let input := fun z => f (jointRead A U z)
    have inj : Function.Injective input := fi.comp (jointRead A U).injective
    have t := ReadComparison.accumulate_trace R L J NL hl (jointRightUnitComparison R L J hl iρ A)
      input v inj vi (fun _ => rfl) G V (fun _ => rfl) (fun _ => rfl) q₀ (fun _ => HEq.rfl)
    exact t.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hr' : RawSingletonTrace w₀ w₂ r₀ r.native :=
    (RawSingletonTrace.ident (fr A)).tensor R L hl hr (dependentUnitFubini_inv_trace R L J hl hr)
  have hs : RawSingletonTrace w₂ w₃ s₀ s.native := by
    unfold s separateRightUnit
    exact independentRightUnitIso_trace R L J _ _ (accCell R L J A) hl iρ
      (dependentWord_nodup A.xs_unique A.us_unique)
  apply AugHom.ext
  exact (hp.comp hq).eq (hr'.comp hs) (fun i => law (a (w₃.read i)) (b (w₃.read i)))

set_option backward.isDefEq.respectTransparency false in
/-- The orientation using the actual nullary Fubini map from the independent unit. -/
theorem actual_fubini_right_unit_forward [IsIso (J.ρ I)] (law : MedialRightUnit R J m) :
    ((independentAugMap R L (J.ρ I) N NR NL hl hr (AugHom.ident (acc A))
       (dependentUnitFubini R L hl hr J).hom).comp (ph A U).hom).comp
        (jointRightUnit R L J NL hl iρ A).hom =
      (separateRightUnit R L J hl iρ A).hom := by
  let e := independentAugIso R L (J.ρ I) N NR NL hl hr
    (NativeAugmentedIso.ident (acc A)) (dependentUnitFubini R L hl hr J)
  change (e.hom.comp (ph A U).hom).comp (jointRightUnit R L J NL hl iρ A).hom = _
  rw [AugHom.comp_assoc, actual_fubini_right_unit R L J N NR NL hl hr iρ m mi h j unit_middle A law]
  change e.hom.comp (e.inv.comp _) = _
  rw [← AugHom.comp_assoc, e.hom_inv, AugHom.ident_comp]

end OrderedDependentAugData
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
