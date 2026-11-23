module
public import ContextualComposition.NativeOrderedDependentData
@[expose] public section

/-! Natural augmented Fubini for fixed ordered arities: two independent
recursive constructions, with the original binary comparison at each node. -/
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
variable (c : T.obj I I ⟶ I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

noncomputable def independentAugIso {A B D E : Aug ℙ I}
    (e : NativeAugmentedIso A B) (f : NativeAugmentedIso D E) :
    NativeAugmentedIso (independentAug R L c A D) (independentAug R L c B E) where
  hom := independentAugMap R L c N NR NL hl hr e.hom f.hom
  inv := independentAugMap R L c N NR NL hl hr e.inv f.inv
  hom_inv := by rw [← independentAugMap_comp, e.hom_inv, f.hom_inv, independentAugMap_ident]
  inv_hom := by rw [← independentAugMap_comp, e.inv_hom, f.inv_hom, independentAugMap_ident]

theorem independentAugMap_square
    {A B D E A' B' D' E' : Aug ℙ I}
    (p : AugHom ℙ A B) (q : AugHom ℙ D E) (p' : AugHom ℙ A' B') (q' : AugHom ℙ D' E')
    (a : AugHom ℙ A A') (b : AugHom ℙ B B') (d : AugHom ℙ D D') (e : AugHom ℙ E E')
    (hp : p.comp b = a.comp p') (hq : q.comp e = d.comp q') :
    (independentAugMap R L c N NR NL hl hr p q).comp (independentAugMap R L c N NR NL hl hr b e) =
    (independentAugMap R L c N NR NL hl hr a d).comp (independentAugMap R L c N NR NL hl hr p' q') := by
  rw [← independentAugMap_comp, ← independentAugMap_comp, hp, hq]

section Fold
variable (J : UnitCompat R I)

/-- Nullary parent and continuation families both have one address, of
coefficient the multiplicative unit. Their augmentations are actual
singleton folds. -/
def OrderedDependentAugData.unit (I : C) : OrderedDependentAugData I where
  X := PUnit.{u+1}
  U := PUnit.{u+1}
  eqX := inferInstance
  eqU := inferInstance
  xs := [PUnit.unit]
  us := fun _ => [PUnit.unit]
  V := fun _ => I
  A := fun _ _ => I
  xs_unique := by simp
  us_unique := by intros; simp
  ε := (ρ_ I).hom
  δ := fun _ => (ρ_ I).hom

noncomputable def OrderedDependentAugArrow.ident (A : OrderedDependentAugData I) : OrderedDependentAugArrow A A :=
  letI := A.eqX
  letI := A.eqU
  ⟨OrderedDependentMap.identity A.xs A.us A.V A.A A.xs_unique A.us_unique,
    OrderedDependentMap.identity_preserves A.xs A.us A.V A.A A.xs_unique A.us_unique A.δ A.ε⟩

include hr in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem OrderedDependentAugArrow.accumulate_ident (A : OrderedDependentAugData I) :
    (OrderedDependentAugArrow.ident A).accumulate R L J N NL hl =
      AugHom.ident (A.accumulate R L J) := by
  letI := A.eqX
  letI := A.eqU
  exact OrderedDependentMap.accumulateAug_ident R L J A.xs A.us A.V A.A N NL hl hr
    A.xs_unique A.us_unique A.ε A.δ

/-- Parent and continuation inputs are jointly tensor-folded first,
independently of any dependent comparison. -/
def dependentInputFold : (n : Nat) → (Fin n → OrderedDependentAugData I) → OrderedDependentAugData I
  | 0, _ => OrderedDependentAugData.unit I
  | 1, A => A 0
  | n + 2, A => (A 0).product R L J (dependentInputFold (n + 1) (fun j => A j.succ))

noncomputable def dependentInputFoldMap :
    (n : Nat) → {A B : Fin n → OrderedDependentAugData I} →
      (∀ j, OrderedDependentAugArrow (A j) (B j)) →
      OrderedDependentAugArrow (dependentInputFold R L J n A) (dependentInputFold R L J n B)
  | 0, _, _, _ => OrderedDependentAugArrow.ident _
  | 1, _, _, p => p 0
  | n + 2, _, _, p =>
    (p 0).product R L J N NR NL hl hr (dependentInputFoldMap (n + 1) (fun j => p j.succ))

set_option backward.isDefEq.respectTransparency false in
include hl hr in
theorem dependentUnit_augCell :
    dependentWordAugCell R L J [PUnit.unit] (fun _ : PUnit.{u+1} => [PUnit.unit])
      (fun _ => I) (fun _ _ => I) (indexedAugmentation (fun _ => (ρ_ I).hom)) (ρ_ I).hom =
      (ρ_ (T.obj I I)).hom ≫ J.ρ I := by
  let t : PUnit.{u+1} × PUnit.{u+1} := (PUnit.unit,PUnit.unit)
  let A := fun _ : PUnit.{u+1} × PUnit.{u+1} => T.obj I I
  let B := indexInput (fun _ _ : PUnit.{u+1} => I) (fun _ => [PUnit.unit])
  let q := fun _ : PUnit.{u+1} => (ρ_ I).hom
  have e : (indexedAugmentation (B:=fun _ (_ : PUnit.{u+1}) => I) (us:=fun _ => [PUnit.unit]) q) = q := by
    funext x
    change eqToHom (rfl : I ⊗ Zₐ = I ⊗ Zₐ) ≫ (ρ_ I).hom = (ρ_ I).hom
    simp only [eqToHom_refl, Category.id_comp]
  have h : dependentWordAugCell R L J [PUnit.unit] (fun _ : PUnit.{u+1} => [PUnit.unit])
      (fun _ => I) (fun _ _ => I) (indexedAugmentation q) (ρ_ I).hom =
      compressGrid A (.bin (.bin (.leaf t) .zero) .zero) ≫
        augmentation L J (fun _ => I) B [PUnit.unit] q (ρ_ I).hom := by
    unfold dependentWordAugCell
    rw [e]
    change 𝟙 _ ≫ compressGrid A (.bin (.bin (.leaf t) .zero) .zero) ≫ 𝟙 _ ≫
      augmentation L J (fun _ => I) B [PUnit.unit] q (ρ_ I).hom = _
    simp only [Category.id_comp]
  rw [h, compressGrid_singleLeaf_nested, ← augmentation_normal]
  rw [reassoc_of% dependent_singleton_chart_unit R L I I (hl I) (hr I)]

set_option backward.isDefEq.respectTransparency false in
/-- The ordered nullary comparison is the inverse of the actual
singleton augmentation, whose coefficient is the multiplicative unitor. -/
noncomputable def dependentUnitFubini [IsIso (J.ρ I)] :
    NativeAugmentedIso (AugHom.unit (S:=ℙ) I) ((OrderedDependentAugData.unit I).accumulate R L J) := by
  let A := (OrderedDependentAugData.unit I).accumulate R L J
  let B := AugHom.unit (S:=ℙ) I
  let f : Fin A.base.n ≃ Fin B.base.n := Equiv.refl (Fin 1)
  let p := A.ε.cell
  have hp (j : Fin B.base.n) : IsIso (p j) := by
    change IsIso (eqToHom (wordFoldPin (fun _ : PUnit.{u+1} × PUnit.{u+1} => T.obj I I)
      [(PUnit.unit,PUnit.unit)] j) ≫ dependentWordAugCell R L J [PUnit.unit]
        (fun _ : PUnit.{u+1} => [PUnit.unit]) (fun _ => I) (fun _ _ => I)
        (indexedAugmentation (fun _ => (ρ_ I).hom)) (ρ_ I).hom)
    rw [dependentUnit_augCell R L hl hr J]
    infer_instance
  let e : NativeFamilyIso A.base B.base :=
    ⟨Hom.mk f p, nativeEquivInv f p hp, nativeEquivInv_right f p hp, nativeEquivInv_left f p hp⟩
  have h : e.hom.comp B.ε = A.ε := by
    change (Hom.mk f p).comp (Hom.ident _) = A.ε
    rw [Hom.comp_ident]
    have z : (f : Fin A.base.n → Fin B.base.n) = A.ε.addr :=
      funext fun i => Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    apply native_hom_ext z
    intro j
    change p j = eqToHom _ ≫ p j
    have hh : eqToHom (congrArg (fun k => standardPushObj k A.base.val j) z) = 𝟙 _ := rfl
    rw [hh]
    exact (Category.id_comp _).symm
  let e' := e.augment h
  exact ⟨e'.inv,e'.hom,e'.inv_hom,e'.hom_inv⟩

section Comparison
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]

noncomputable def orderedFubini :
    (n : Nat) → (A : Fin n → OrderedDependentAugData I) →
      NativeAugmentedIso
        (independentAugFold R L (J.ρ I) n (fun t => (A t).accumulate R L J))
        ((dependentInputFold R L J n A).accumulate R L J)
  | 0, _ => dependentUnitFubini R L hl hr J
  | 1, _ => NativeAugmentedIso.ident _
  | n + 2, A =>
    let B := dependentInputFold R L J (n + 1) (fun t => A t.succ)
    let e := orderedFubini (n + 1) (fun t => A t.succ)
    (independentAugIso R L (J.ρ I) N NR NL hl hr (NativeAugmentedIso.ident ((A 0).accumulate R L J)) e).trans
      ((A 0).binaryFubini R L J N NR NL hl hr m mi h j unit_middle B)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem orderedFubini_natural :
    (n : Nat) → {A B : Fin n → OrderedDependentAugData I} →
      (p : ∀ j, OrderedDependentAugArrow (A j) (B j)) →
      (independentAugFoldMap R L (J.ρ I) N NR NL hl hr n (fun j => (p j).accumulate R L J N NL hl)).comp
        (orderedFubini R L N NR NL hl hr J m mi h j unit_middle n B).hom =
      (orderedFubini R L N NR NL hl hr J m mi h j unit_middle n A).hom.comp
        ((dependentInputFoldMap R L N NR NL hl hr J n p).accumulate R L J N NL hl)
  | 0, _, _, _ => by
    simp only [independentAugFoldMap, orderedFubini, dependentInputFoldMap, AugHom.ident_comp]
    change _ = (dependentUnitFubini R L hl hr J).hom.comp
      ((OrderedDependentAugArrow.ident (OrderedDependentAugData.unit I)).accumulate R L J N NL hl)
    rw [OrderedDependentAugArrow.accumulate_ident R L N NL hl hr J, AugHom.comp_ident]
  | 1, _, _, _ => by
    simp only [independentAugFoldMap, orderedFubini, dependentInputFoldMap,
      NativeAugmentedIso.ident, AugHom.ident_comp, AugHom.comp_ident]
  | n + 2, A, B, p => by
    let A' := dependentInputFold R L J (n + 1) (fun t => A t.succ)
    let B' := dependentInputFold R L J (n + 1) (fun t => B t.succ)
    let P := dependentInputFoldMap R L N NR NL hl hr J (n + 1) (fun t => p t.succ)
    let e := orderedFubini R L N NR NL hl hr J m mi h j unit_middle (n + 1) (fun t => A t.succ)
    let f := orderedFubini R L N NR NL hl hr J m mi h j unit_middle (n + 1) (fun t => B t.succ)
    let a := (p 0).accumulate R L J N NL hl
    let b := independentAugFoldMap R L (J.ρ I) N NR NL hl hr (n + 1)
      (fun t => (p t.succ).accumulate R L J N NL hl)
    let q := P.accumulate R L J N NL hl
    let aa := AugHom.ident ((A 0).accumulate R L J)
    let bb := AugHom.ident ((B 0).accumulate R L J)
    let x := (A 0).binaryFubini R L J N NR NL hl hr m mi h j unit_middle A'
    let y := (B 0).binaryFubini R L J N NR NL hl hr m mi h j unit_middle B'
    let z := ((p 0).product R L J N NR NL hl hr P).accumulate R L J N NL hl
    let H := fun {A B D E : Aug ℙ I} (p : AugHom ℙ A B) (q : AugHom ℙ D E) =>
      independentAugMap R L (J.ρ I) N NR NL hl hr p q
    have h₁ : b.comp f.hom = e.hom.comp q := orderedFubini_natural (n + 1) (fun t => p t.succ)
    have h₂ : a.comp bb = aa.comp a := (AugHom.comp_ident _).trans (AugHom.ident_comp _).symm
    have h₃ : (H a b).comp (H bb f.hom) = (H aa e.hom).comp (H a q) :=
      independentAugMap_square R L (J.ρ I) N NR NL hl hr a b a q aa bb e.hom f.hom h₂ h₁
    have h₄ : (H a q).comp y.hom = x.hom.comp z :=
      OrderedDependentAugArrow.binaryFubini_natural R L J N NR NL hl hr m mi h j unit_middle (p 0) P
    change (H a b).comp ((H bb f.hom).comp y.hom) = ((H aa e.hom).comp x.hom).comp z
    rw [← AugHom.comp_assoc, h₃, AugHom.comp_assoc, h₄, AugHom.comp_assoc]

/-- Read both raw tags of an actual accumulated native position. -/
noncomputable def OrderedDependentAugData.read (A : OrderedDependentAugData I)
    (i : Fin (A.accumulate R L J).base.n) : A.X × A.U :=
  (dependentWord A.xs A.us)[i]

/-- The original right-hand output index contains a nested product of
parent positions and a nested product of child positions. Read these as
the tuple of pairs, without erasing any coefficient repetitions. -/
def dependentInputFoldRead :
    (n : Nat) → (A : Fin n → OrderedDependentAugData I) →
      (dependentInputFold R L J n A).X × (dependentInputFold R L J n A).U →
      (∀ j, (A j).X × (A j).U)
  | 0, _, _ => fun j => j.elim0
  | 1, _, x => Fin.cases x (fun j => j.elim0)
  | n + 2, A, x => Fin.cases (x.1.1,x.2.1)
      (dependentInputFoldRead (n + 1) (fun j => A j.succ) (x.1.2,x.2.2))

set_option backward.isDefEq.respectTransparency false in
omit [IsIso (J.ρ I)] in
theorem OrderedDependentAugData.binaryFubini_read_pair (A B : OrderedDependentAugData I)
    (i : Fin (independentAug R L (J.ρ I) (A.accumulate R L J) (B.accumulate R L J)).base.n) :
    let k := (A.binaryFubini R L J N NR NL hl hr m mi h j unit_middle B).hom.native.addr i
    let q := (A.product R L J B).read R L J k
    let t := independentPairEquiv (A.accumulate R L J).base (B.accumulate R L J).base i
    ((q.1.1,q.2.1),(q.1.2,q.2.2)) = (A.read R L J t.1,B.read R L J t.2) := by
  intro k q t
  let f := fun p : A.X × A.U × B.X × B.U => ((p.1,p.2.1),(p.2.2.1,p.2.2.2))
  have h' := binaryProductAugIso_addr R L J A.xs B.xs A.us B.us A.V B.V A.A B.A A.δ B.δ A.ε B.ε
    N NR NL m mi h j unit_middle hl hr
    (occurrenceWord_nodup (dependentWord_nodup A.xs_unique A.us_unique)
      (dependentWord_nodup B.xs_unique B.us_unique)) i
  exact congrArg f h'

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
theorem orderedFubini_read :
    (n : Nat) → (A : Fin n → OrderedDependentAugData I) →
    (i : Fin (independentAugFold R L (J.ρ I) n (fun t => (A t).accumulate R L J)).base.n) →
    dependentInputFoldRead R L J n A
      ((dependentInputFold R L J n A).read R L J
        ((orderedFubini R L N NR NL hl hr J m mi h j unit_middle n A).hom.native.addr i)) =
    fun k => (A k).read R L J
      (independentAugFoldRead R L (J.ρ I) n (fun t => (A t).accumulate R L J) i k)
  | 0, _, _ => funext fun j => j.elim0
  | 1, _, _ => by
    funext j
    have e : j = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
    subst j
    rfl
  | n + 2, A, i => by
    let AA := fun t : Fin (n + 2) => (A t).accumulate R L J
    let a := independentAugFold R L (J.ρ I) (n + 1) (fun t => AA t.succ)
    let b := dependentInputFold R L J (n + 1) (fun t => A t.succ)
    let f := orderedFubini R L N NR NL hl hr J m mi h j unit_middle (n + 1) (fun t => A t.succ)
    let m₁ := independentAugMap R L (J.ρ I) N NR NL hl hr (AugHom.ident (AA 0)) f.hom
    let m₂ := (A 0).binaryFubini R L J N NR NL hl hr m mi h j unit_middle b
    let k := m₁.native.addr i
    let z := m₂.hom.native.addr k
    let t := independentPairEquiv (AA 0).base a.base i
    let s := independentPairEquiv (AA 0).base (b.accumulate R L J).base k
    let w := ((A 0).product R L J b).read R L J z
    have h₁ : s = (t.1,f.hom.native.addr t.2) := by
      change independentPairEquiv _ _ ((independentNativeWordMap T (Hom.ident (AA 0).base) f.hom.native R L).addr i) = _
      exact independentPairEquiv_addr R L (Hom.ident (AA 0).base) f.hom.native i
    have h₂ : ((w.1.1,w.2.1),(w.1.2,w.2.2)) = ((A 0).read R L J s.1,b.read R L J s.2) :=
      (A 0).binaryFubini_read_pair R L N NR NL hl hr J m mi h j unit_middle b k
    rw [h₁] at h₂
    have h₃ := orderedFubini_read (n + 1) (fun t => A t.succ) t.2
    funext j'
    refine Fin.cases ?_ (fun l => ?_) j'
    · change Fin.cases (w.1.1,w.2.1) _ 0 = (A 0).read R L J (Fin.cases t.1 _ 0)
      simp only [Fin.cases_zero]
      exact congrArg Prod.fst h₂
    · change (dependentInputFoldRead R L J (n + 1) (fun t => A t.succ) (w.1.2,w.2.2)) l =
        (A l.succ).read R L J (independentAugFoldRead R L (J.ρ I) (n + 1) (fun t => AA t.succ) t.2 l)
      exact (congrArg (fun x : b.X × b.U => dependentInputFoldRead R L J (n + 1) (fun t => A t.succ) x l)
        (congrArg Prod.snd h₂)).trans (congrFun h₃ l)

end Comparison

end Fold
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
