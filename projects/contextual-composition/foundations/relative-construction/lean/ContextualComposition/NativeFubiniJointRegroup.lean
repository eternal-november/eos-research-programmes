module
public import ContextualComposition.NativeFubiniPairFrame
@[expose] public section

/-! The independent associator on the bookkeeping side of Fubini,
lifted through both slots of the original dependent augmentation. -/
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
variable (P : TensorPrimitive T)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))

set_option backward.isDefEq.respectTransparency false in
include NR NL Q U hl hr in
theorem independentAssoc_preserves_pullback {X Y W : Type u} (A : X → C) (B : Y → C) (D : W → C)
    (xs : List X) (ys : List Y) (ws : List W)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I) (d : fold 𝒮 Zₐ D ws ⟶ I) :
    let w₀ := (xs.product ys).product ws
    let _w₁ := xs.product (ys.product ws)
    let C₁ := crossLabel T A (crossLabel T B D)
    let e := (std_fold_map C₁ tripleRetag w₀).symm.trans
      (congrArg (fold 𝒮 Zₐ C₁) (tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)))
    act 𝒮 Zₐ (fun z : (X × Y) × W => P.assoc (A z.1.1) (B z.1.2) (D z.2)) w₀ ≫
      eqToHom e ≫ independentAssocRightAug R L J A B D xs ys ws a b d =
      independentAssocLeftAug R L J A B D xs ys ws a b d := by
  intro w₀ w₁ C₁ e
  let s := independentAssocLeftAug R L J A B D xs ys ws a b d
  let t := independentAssocRightAug R L J A B D xs ys ws a b d
  let g := tripleRetag (X:=X) (Y:=Y) (W:=W)
  let p := fun z : X × Y × W => P.assoc (A z.1) (B z.2.1) (D z.2.2)
  have h := independentAssocAug_heq R L J P NR NL Q U A B D xs ys ws a b d hl hr
  exact wordAct_preservation_read g w₀ w₁ (tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)) p h
    (hom_source_pin_heq e t) rfl

namespace OrderedDependentAugData
variable (A B D : OrderedDependentAugData I)
set_option quotPrecheck false in
local notation "L₀" => (A.product R L J B).product R L J D
set_option quotPrecheck false in
local notation "L₁" => A.product R L J (B.product R L J D)
set_option quotPrecheck false in
local notation "pRead" => (tripleRetag (X:=A.X) (Y:=B.X) (W:=D.X))
set_option quotPrecheck false in
local notation "qRead" => (tripleRetag (X:=A.U) (Y:=B.U) (W:=D.U))

set_option backward.isDefEq.respectTransparency false in
noncomputable def jointRegroup :
    NativeAugmentedIso ((L₀).accumulate R L J) ((L₁).accumulate R L J) := by
  let f := pRead
  let g := fun _ : (L₀).X => qRead
  let p (t : (L₀).X) : (L₀).V t ≅ (L₁).V (f t) := by
    let _ := ι (A.V t.1.1) (B.V t.1.2) (D.V t.2)
    exact asIso (P.assoc (A.V t.1.1) (B.V t.1.2) (D.V t.2))
  let q (t : (L₀).X) (s : (L₀).U) : (L₀).A t s ≅ (L₁).A (f t) (g t s) := by
    let _ := ι (A.A t.1.1 s.1.1) (B.A t.1.2 s.1.2) (D.A t.2 s.2)
    exact asIso (P.assoc (A.A t.1.1 s.1.1) (B.A t.1.2 s.1.2) (D.A t.2 s.2))
  exact dependentBothRetagIso R L J NL f (fun x y => g x y) (L₀).xs (L₁).xs (L₀).us (L₁).us
    (tripleRetag_word A.xs (fun _ => B.xs) (fun _ _ => D.xs))
    (fun t => tripleRetag_word (A.us t.1.1) (fun _ => B.us t.1.2) (fun _ _ => D.us t.2))
    (L₀).ε (L₁).ε (L₀).δ (L₁).δ p q
    (independentAssoc_preserves_pullback R L J P NR NL Q U hl hr A.V B.V D.V A.xs B.xs D.xs A.ε B.ε D.ε)
    (fun t => independentAssoc_preserves_pullback R L J P NR NL Q U hl hr
      (A.A t.1.1) (B.A t.1.2) (D.A t.2) (A.us t.1.1) (B.us t.1.2) (D.us t.2)
      (A.δ t.1.1) (B.δ t.1.2) (D.δ t.2))
    (dependentWord_nodup (L₀).xs_unique (L₀).us_unique)


abbrev TripleBranch := A.Branch × B.Branch × D.Branch

def groupedLeftRead : (L₀).Branch ≃ TripleBranch A B D :=
  (jointRead (A.product R L J B) D).trans
    (((jointRead A B).prodCongr (Equiv.refl D.Branch)).trans tripleRetag)

def groupedRightRead : (L₁).Branch ≃ TripleBranch A B D :=
  (jointRead A (B.product R L J D)).trans ((Equiv.refl A.Branch).prodCongr (jointRead B D))

def groupedLeftLabel (z : TripleBranch A B D) :=
  T.obj (T.obj (T.obj (A.V z.1.1) (B.V z.2.1.1)) (D.V z.2.2.1))
    (T.obj (T.obj (A.A z.1.1 z.1.2) (B.A z.2.1.1 z.2.1.2)) (D.A z.2.2.1 z.2.2.2))

def groupedRightLabel (z : TripleBranch A B D) :=
  T.obj (T.obj (A.V z.1.1) (T.obj (B.V z.2.1.1) (D.V z.2.2.1)))
    (T.obj (A.A z.1.1 z.1.2) (T.obj (B.A z.2.1.1 z.2.1.2) (D.A z.2.2.1 z.2.2.2)))

noncomputable def groupedLeftFrame :
    RawSingletonFrame (TripleBranch A B D) ((L₀).accumulate R L J).base :=
  let f := groupedLeftRead R L J A B D
  ((L₀).accFrame R L J).relabel f f.injective (groupedLeftLabel (T:=T) A B D) (fun _ => rfl)

noncomputable def groupedRightFrame :
    RawSingletonFrame (TripleBranch A B D) ((L₁).accumulate R L J).base :=
  let f := groupedRightRead R L J A B D
  ((L₁).accFrame R L J).relabel f f.injective (groupedRightLabel (T:=T) A B D) (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2900000 in
theorem jointRegroup_trace :
    RawSingletonTrace (groupedLeftFrame R L J A B D) (groupedRightFrame R L J A B D)
      (fun z => T.map (P.assoc (A.V z.1.1) (B.V z.2.1.1) (D.V z.2.2.1))
        (P.assoc (A.A z.1.1 z.1.2) (B.A z.2.1.1 z.2.1.2) (D.A z.2.2.1 z.2.2.2)))
      (jointRegroup R L J P NR NL Q U hl hr ι A B D).hom.native := by
  unfold jointRegroup groupedLeftFrame groupedRightFrame accFrame
  dsimp only
  exact dependentBothRetagIso_trace R L J NL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (groupedLeftRead R L J A B D) (groupedRightRead R L J A B D) _ _ (fun _ => rfl)
    (groupedLeftLabel (T:=T) A B D) (groupedRightLabel (T:=T) A B D)
    (fun _ => rfl) (fun _ => rfl) _ (fun _ => HEq.rfl)

end OrderedDependentAugData

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
