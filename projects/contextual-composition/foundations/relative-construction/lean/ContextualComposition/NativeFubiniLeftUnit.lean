module
public import ContextualComposition.NativeFubiniRightUnit
@[expose] public section

/-! The left Fubini unit square follows from the actual swap square, the
actual right unit square, and naturality at the nullary collapse. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (ι : ∀ a b, IsIso (P.swap a b))
variable {X : Type u} (A : X → C) (xs : List X)
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)

set_option backward.isDefEq.respectTransparency false in
noncomputable def independentUnitSwap (hx : xs.Nodup) :
    NativeAugmentedIso (independentAug R L (J.ρ I) (AugHom.unit (S:=ℙ) I) (wordAug A xs p))
      (independentAug R L (J.ρ I) (wordAug A xs p) (AugHom.unit (S:=ℙ) I)) :=
  let B := fun _ : PUnit.{u+1} => I
  let ys : List PUnit.{u+1} := [PUnit.unit]
  (independentSwapIso R L J P Q N swap_unit ι B A ys xs (ρ_ I).hom p (by simp [ys]) hx).retarget
    (congrArg (fun U => independentAug R L (J.ρ I) U (wordAug A xs p)) unit_wordAug.symm)
    (congrArg (independentAug R L (J.ρ I) (wordAug A xs p)) unit_wordAug.symm)

set_option backward.isDefEq.respectTransparency false in
theorem independentUnitSwap_trace (hx : xs.Nodup) :
    let U : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
      rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
    let F := U.tensor T (rawWordFrame A xs hx)
    let e := Equiv.prodComm X PUnit.{u+1}
    let G := ((rawWordFrame A xs hx).tensor T U).relabel e e.injective
      (fun z => T.obj (A z.2) I) (fun _ => rfl)
    RawSingletonTrace F G (fun z => P.swap I (A z.2))
      (independentUnitSwap R L J P Q N swap_unit ι A xs p hx).hom.native := by
  intro U F e G
  let B := fun _ : PUnit.{u+1} => I
  let ys : List PUnit.{u+1} := [PUnit.unit]
  let hy : ys.Nodup := by simp [ys]
  let a := independentSwapIso R L J P Q N swap_unit ι B A ys xs (ρ_ I).hom p hy hx
  have h := independentSwapIso_trace R L J P Q N swap_unit ι B A ys xs (ρ_ I).hom p hy hx
  have k : HEq a.hom.native (independentUnitSwap R L J P Q N swap_unit ι A xs p hx).hom.native := by
    unfold independentUnitSwap
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  exact h.retarget rfl rfl k (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

namespace OrderedDependentAugData
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (iρ : ∀ a, IsIso (J.ρ a))
variable (D : OrderedDependentAugData I)

local notation "prd" => product R L J
local notation "acc" => accumulate R L J
local notation "fr" => accFrame R L J
local notation "U" => OrderedDependentAugData.unit I
local notation "nSwap" => separateSwap R L J P N Q swap_unit ι
local notation "nMap" => independentAugMap R L (J.ρ I) N NR NL hl hr
local notation "e" => dependentUnitFubini R L hl hr J

noncomputable def jointLeftUnit :=
  (jointSwap R L J P N NL Q hl swap_unit ι U D).trans (jointRightUnit R L J NL hl iρ D)

noncomputable def separateUnitSwap :=
  independentUnitSwap R L J P Q N swap_unit ι (dependentLabels (T:=T) D.V D.A) (dependentWord D.xs D.us)
    (accCell R L J D) (dependentWord_nodup D.xs_unique D.us_unique)

noncomputable def separateLeftUnit :=
  (separateUnitSwap R L J P Q N swap_unit ι D).trans (separateRightUnit R L J hl iρ D)


set_option backward.isDefEq.respectTransparency false in
omit rF in
theorem separateLeftUnit_trace :
    let U₀ : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
      rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
    let F := U₀.tensor T (fr D)
    let read := fun x : D.Branch => ((PUnit.unit : PUnit.{u+1}), x)
    let G := (fr D).relabel read (fun _ _ h => congrArg Prod.snd h) (fun z => (fr D).label z.2) (fun _ => rfl)
    RawSingletonTrace F G (fun z => depLeftUnitCell R J P ((fr D).label z.2))
      (separateLeftUnit R L J P Q N swap_unit ι hl iρ D).hom.native := by
  intro U₀ F read G
  let swap := Equiv.prodComm D.Branch PUnit.{u+1}
  let cf : D.Branch → C := (fr D).label
  let K := ((fr D).tensor T U₀).relabel swap swap.injective (fun z => T.obj (cf z.2) I) (fun _ => rfl)
  have h := independentUnitSwap_trace R L J P Q N swap_unit ι _ _ (accCell R L J D)
    (dependentWord_nodup D.xs_unique D.us_unique)
  have h₀ : RawSingletonTrace F K (fun z => P.swap I (cf z.2))
      (separateUnitSwap R L J P Q N swap_unit ι D).hom.native := h
  have h₁ : RawSingletonTrace K G (fun z => J.ρ (cf z.2))
      (separateRightUnit R L J hl iρ D).hom.native := by
    have t := (independentRightUnitIso_trace R L J _ _ (accCell R L J D) hl iρ
      (dependentWord_nodup D.xs_unique D.us_unique)).relabel swap swap.injective
        (fun z => T.obj (cf z.2) I) (fun z => cf z.2) (fun _ => rfl) (fun _ => rfl)
        (fun z => J.ρ (cf z.2)) (fun _ => HEq.rfl)
    exact t.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  exact h₀.comp h₁

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
theorem nullary_swap_natural [IsIso (J.ρ I)] :
    (nSwap U D).hom.comp (nMap (AugHom.ident (acc D)) (e).inv) =
    (nMap (e).inv (AugHom.ident (acc D))).comp (separateUnitSwap R L J P Q N swap_unit ι D).hom := by
  let Ω := PUnit.{u+1} × D.Branch
  let V (z : Ω) := T.obj (D.V z.2.1) (D.A z.2.1 z.2.2)
  let u : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
    rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
  let t := Equiv.prodComm D.Branch PUnit.{u+1}
  let F (z : Ω) := T.obj (T.obj I I) (V z)
  let G (z : Ω) := T.obj (V z) (T.obj I I)
  let H (z : Ω) := T.obj I (V z)
  let K (z : Ω) := T.obj (V z) I
  let a (z : Ω) : F z ⟶ G z := P.swap (T.obj I I) (V z)
  let b (z : Ω) : G z ⟶ K z := T.map (𝟙 (V z)) (J.ρ I)
  let c (z : Ω) : F z ⟶ H z := T.map (J.ρ I) (𝟙 (V z))
  let d (z : Ω) : H z ⟶ K z := P.swap I (V z)
  let w₀ := (nullaryFrame R L J).tensor T (fr D)
  let w₁ := ((fr D).tensor T (nullaryFrame R L J)).relabel t t.injective G (fun _ => rfl)
  let w₂ := u.tensor T (fr D)
  let w₃ := ((fr D).tensor T u).relabel t t.injective K (fun _ => rfl)
  have ha : RawSingletonTrace w₀ w₁ a (nSwap U D).hom.native := by
    let f : (U).Branch × D.Branch → Ω := fun z => (PUnit.unit,z.2)
    have fi : Function.Injective f := fun _ _ eq => Prod.ext (nullaryBranch_eq _ _) (congrArg (fun z : Ω => z.2) eq)
    have h := (independentSwapIso_trace R L J P Q N swap_unit ι
      (dependentLabels (T:=T) (U).V (U).A) (dependentLabels (T:=T) D.V D.A)
      (dependentWord (U).xs (U).us) (dependentWord D.xs D.us) (accCell R L J U) (accCell R L J D)
      (dependentWord_nodup (U).xs_unique (U).us_unique) (dependentWord_nodup D.xs_unique D.us_unique)).relabel
        f fi F G (fun _ => rfl) (fun _ => rfl) a (fun _ => HEq.rfl)
    exact h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hb : RawSingletonTrace w₁ w₃ b (nMap (AugHom.ident (acc D)) (e).inv).native := by
    exact ((RawSingletonTrace.ident (fr D)).tensor R L hl hr (dependentUnitFubini_inv_trace R L J hl hr)).relabel
      t t.injective G K (fun _ => rfl) (fun _ => rfl) b (fun _ => HEq.rfl)
  have hc : RawSingletonTrace w₀ w₂ c (nMap (e).inv (AugHom.ident (acc D))).native :=
    (dependentUnitFubini_inv_trace R L J hl hr).tensor R L hl hr (RawSingletonTrace.ident (fr D))
  have hd : RawSingletonTrace w₂ w₃ d (separateUnitSwap R L J P Q N swap_unit ι D).hom.native :=
    independentUnitSwap_trace R L J P Q N swap_unit ι _ _ (accCell R L J D)
      (dependentWord_nodup D.xs_unique D.us_unique)
  apply AugHom.ext
  exact (ha.comp hb).eq (hc.comp hd) (fun i => (P.swap_nat (J.ρ I) (𝟙 (V (w₃.read i)))).symm)

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
local notation "ph" => binaryFubini R L J N NR NL hl hr m mi h j unit_middle

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5000000 in
theorem actual_fubini_left_unit [IsIso (J.ρ I)]
    (rightLaw : MedialRightUnit R J m) (symLaw : MedialSwap P m) :
    (ph U D).hom.comp (jointLeftUnit R L J P Q N swap_unit ι NL hl iρ D).hom =
      (nMap (e).inv (AugHom.ident (acc D))).comp (separateLeftUnit R L J P Q N swap_unit ι hl iρ D).hom := by
  let r := (jointRightUnit R L J NL hl iρ D).hom
  let s := (separateRightUnit R L J hl iρ D).hom
  let b := (jointSwap R L J P N NL Q hl swap_unit ι U D).hom
  let c := (nSwap U D).hom
  let d := (separateUnitSwap R L J P Q N swap_unit ι D).hom
  change (ph U D).hom.comp (b.comp r) = (nMap (e).inv (AugHom.ident (acc D))).comp (d.comp s)
  rw [← AugHom.comp_assoc, actual_fubini_swap R L J P N NR NL Q hl hr swap_unit ι m mi h j unit_middle U D symLaw]
  rw [AugHom.comp_assoc, actual_fubini_right_unit R L J N NR NL hl hr iρ m mi h j unit_middle D rightLaw]
  rw [← AugHom.comp_assoc, nullary_swap_natural R L J P Q N swap_unit ι NR NL hl hr D, AugHom.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem actual_fubini_left_unit_forward [IsIso (J.ρ I)]
    (rightLaw : MedialRightUnit R J m) (symLaw : MedialSwap P m) :
    ((nMap (e).hom (AugHom.ident (acc D))).comp (ph U D).hom).comp
        (jointLeftUnit R L J P Q N swap_unit ι NL hl iρ D).hom =
      (separateLeftUnit R L J P Q N swap_unit ι hl iρ D).hom := by
  let f := independentAugIso R L (J.ρ I) N NR NL hl hr (e) (NativeAugmentedIso.ident (acc D))
  change (f.hom.comp (ph U D).hom).comp (jointLeftUnit R L J P Q N swap_unit ι NL hl iρ D).hom = _
  rw [AugHom.comp_assoc,
    actual_fubini_left_unit R L J P Q N swap_unit ι NR NL hl hr iρ D m mi h j unit_middle rightLaw symLaw]
  change f.hom.comp (f.inv.comp _) = _
  rw [← AugHom.comp_assoc, f.hom_inv, AugHom.ident_comp]

end OrderedDependentAugData
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
