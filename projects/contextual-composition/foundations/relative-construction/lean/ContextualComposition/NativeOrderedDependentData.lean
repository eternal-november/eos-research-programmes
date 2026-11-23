module
public import ContextualComposition.NativeBinaryProductComparison
@[expose] public section

/-! Ordered augmented dependent inputs closed under literal independent product. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

/-- The address type and its chosen finite word are separate; none of the
labels or proof-relevant empty-fibre arrows is quotiented. -/
structure OrderedDependentAugData (I : C) where
  X : Type u
  U : Type u
  eqX : DecidableEq X
  eqU : DecidableEq U
  xs : List X
  us : X → List U
  V : X → C
  A : X → U → C
  xs_unique : xs.Nodup
  us_unique : ∀ x ∈ xs, (us x).Nodup
  ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I
  δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (A x) (us x) ⟶ I

structure OrderedDependentAugArrow {I : C} (A B : OrderedDependentAugData I) where
  map : @OrderedDependentMap C _ _ _ A.X A.U B.X B.U B.eqX B.eqU A.xs A.us B.xs B.us A.V A.A B.V B.A
  preserves :
    letI := B.eqX
    letI := B.eqU
    map.Preserves B.xs_unique (fun x h => B.us_unique _ (map.parent_mem x h)) A.δ B.δ A.ε B.ε

variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

namespace OrderedDependentAugData

noncomputable def accumulate (A : OrderedDependentAugData I) : Aug ℙ I :=
  dependentWordAug R L J A.xs A.us A.V A.A (indexedAugmentation A.δ) A.ε

def product (A B : OrderedDependentAugData I) : OrderedDependentAugData I where
  X := A.X × B.X
  U := A.U × B.U
  eqX := @instDecidableEqProd A.X B.X A.eqX B.eqX
  eqU := @instDecidableEqProd A.U B.U A.eqU B.eqU
  xs := A.xs.product B.xs
  us := crossChildWord A.us B.us
  V := crossLabel T A.V B.V
  A := crossChildLabel T A.A B.A
  xs_unique := nodup_product_word A.xs_unique B.xs_unique
  us_unique t ht :=
    let u := (mem_ordered_product A.xs B.xs t).mp ht
    nodup_product_word (A.us_unique t.1 u.1) (B.us_unique t.2 u.2)
  ε := rectangularWordAugCell R L (J.ρ I) A.V B.V A.xs B.xs A.ε B.ε
  δ t := rectangularWordAugCell R L (J.ρ I) (A.A t.1) (B.A t.2)
    (A.us t.1) (B.us t.2) (A.δ t.1) (B.δ t.2)

end OrderedDependentAugData

namespace OrderedDependentAugArrow
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
noncomputable def accumulate {A B : OrderedDependentAugData I} (p : OrderedDependentAugArrow A B) :
    AugHom ℙ (A.accumulate R L J) (B.accumulate R L J) :=
  letI := A.eqX
  letI := B.eqX
  letI := B.eqU
  OrderedDependentMap.accumulateAug R L J p.map N NL hl A.xs_unique B.xs_unique A.us_unique B.us_unique p.preserves

set_option backward.isDefEq.respectTransparency false in
noncomputable def product {A B D E : OrderedDependentAugData I}
    (p : OrderedDependentAugArrow A B) (q : OrderedDependentAugArrow D E) :
    OrderedDependentAugArrow (A.product R L J D) (B.product R L J E) :=
  letI := B.eqX
  letI := B.eqU
  letI := E.eqX
  letI := E.eqU
  ⟨p.map.independentProduct q.map R L,
    OrderedDependentMap.independentProduct_preserves R L (J.ρ I) p.map q.map N NR NL hl hr
      p.preserves q.preserves⟩

end OrderedDependentAugArrow
section Comparison
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)

set_option backward.isDefEq.respectTransparency false in
noncomputable def OrderedDependentAugData.binaryFubini (A B : OrderedDependentAugData I) :
    NativeAugmentedIso (independentAug R L (J.ρ I) (A.accumulate R L J) (B.accumulate R L J))
      ((A.product R L J B).accumulate R L J) :=
  binaryProductAugIso R L J A.xs B.xs A.us B.us A.V B.V A.A B.A A.δ B.δ A.ε B.ε N NR NL m mi h j unit_middle hl hr
    (occurrenceWord_nodup (dependentWord_nodup A.xs_unique A.us_unique) (dependentWord_nodup B.xs_unique B.us_unique))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
set_option linter.style.haveILetI false in
theorem OrderedDependentAugArrow.binaryFubini_natural {A B D E : OrderedDependentAugData I}
    (p : OrderedDependentAugArrow A B) (q : OrderedDependentAugArrow D E) :
    (independentAugMap R L (J.ρ I) N NR NL hl hr (p.accumulate R L J N NL hl) (q.accumulate R L J N NL hl)).comp
      (B.binaryFubini R L J N NR NL hl hr m mi h j unit_middle E).hom =
    (A.binaryFubini R L J N NR NL hl hr m mi h j unit_middle D).hom.comp
      ((p.product R L J N NR NL hl hr q).accumulate R L J N NL hl) := by
  letI := A.eqX
  letI := B.eqX
  letI := B.eqU
  letI := D.eqX
  letI := E.eqX
  letI := E.eqU
  let x := actual_binary_augmented_square_of_orderedInputs (D:=p.map) (E:=q.map) (R:=R) (L:=L) (J:=J) (m:=m) N NR NL hl hr
    A.xs_unique D.xs_unique B.xs_unique E.xs_unique A.us_unique D.us_unique B.us_unique E.us_unique
    p.preserves q.preserves mi h j unit_middle
  let a := separateProductAug_eq R L J A.xs D.xs A.us D.us A.V D.V A.A D.A A.δ D.δ A.ε D.ε hl hr
  let b := separateProductAug_eq R L J B.xs E.xs B.us E.us B.V E.V B.A E.A B.δ E.δ B.ε E.ε hl hr
  let d := jointProductAug_eq R L J A.xs D.xs A.us D.us A.V D.V A.A D.A A.δ D.δ A.ε D.ε hl hr
  let e := jointProductAug_eq R L J B.xs E.xs B.us E.us B.V E.V B.A E.A B.δ E.δ B.ε E.ε hl hr
  let X := independentAugMap R L (J.ρ I) N NR NL hl hr (p.accumulate R L J N NL hl) (q.accumulate R L J N NL hl)
  let Y := (p.product R L J N NR NL hl hr q).accumulate R L J N NL hl
  have h₁ : HEq X.native x.separate.native :=
    (separateBinaryMap_product_heq p.map q.map R L hl hr
      (dependentWord_nodup B.xs_unique B.us_unique) (dependentWord_nodup E.xs_unique E.us_unique)
      (occurrenceWord_nodup (dependentWord_nodup B.xs_unique B.us_unique)
        (dependentWord_nodup E.xs_unique E.us_unique))).trans (heq_of_eq x.separate_native.symm)
  have h₂ : HEq Y.native x.joint.native :=
    (jointBinaryMap_product_heq p.map q.map R L
      (occurrenceWord_nodup (dependentWord_nodup B.xs_unique B.us_unique)
        (dependentWord_nodup E.xs_unique E.us_unique))
      (dependentWord_nodup (B.product R L J E).xs_unique (B.product R L J E).us_unique) hl hr).trans
      (heq_of_eq x.joint_native.symm)
  exact NativeAugmentedIso.retarget_square a.symm b.symm d.symm e.symm _ _ x.separate x.joint X Y
    (augmentHom_heq_native_of_eq _ _ a.symm b.symm h₁.symm)
    (augmentHom_heq_native_of_eq _ _ d.symm e.symm h₂.symm)
    x.commutes

end Comparison

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
