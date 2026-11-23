module
public import ContextualComposition.NativeDependentPresentation
public import ContextualComposition.NativeFubiniTreeWhisker
public import ContextualComposition.NativeFubiniScalarOrder
@[expose] public section

/-! Fubini transports along independent additive presentation changes at
every leaf, using simultaneously the actual separate tensor and the joint
parent-and-continuation structural comparison. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {I : C}

set_option backward.isDefEq.respectTransparency false in
noncomputable def WordAugReadComparison.reorder {W : Type u} (A : W → C) {xs ys : List W}
    (p : AddressOrder W xs ys) (a : fold 𝒮 Zₐ A xs ⟶ I) :
    WordAugReadComparison A A xs ys a ((orderSumIso A p).inv ≫ a) := by
  let b := (orderSumIso A p).inv ≫ a
  refine ofScalarOrder (Equiv.refl W) id xs ys xs ys (List.map_id _) (List.map_id _)
    (fun x => Iso.refl (A x)) a b a b HEq.rfl HEq.rfl p ?_
  have h : act 𝒮 Zₐ (fun x => 𝟙 (A x)) ys = 𝟙 _ := occurrence_act_id A ys
  change (orderSumIso A p).hom ≫ act 𝒮 Zₐ (fun x => 𝟙 (A x)) ys ≫ (orderSumIso A p).inv ≫ a = a
  rw [h, Category.id_comp, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
noncomputable def OrderedDependentAugData.reorderRead (A : OrderedDependentAugData I)
    {xs : List A.X} {us : A.X → List A.U}
    (e : AddressOrder A.X A.xs xs) (d : ∀ x, AddressOrder A.U (A.us x) (us x)) :
    A.ReadComparison (A.reorder e d) where
  parent := WordAugReadComparison.reorder A.V e A.ε
  child x := WordAugReadComparison.reorder (A.A x) (d x) (A.δ x)

set_option backward.isDefEq.respectTransparency false in
noncomputable def OrderedDependentAugData.identRead (A : OrderedDependentAugData I) :
    A.ReadComparison A where
  parent := WordAugReadComparison.ident A.V A.xs A.ε A.xs_unique
  child x := WordAugReadComparison.ofScalarOrder (Equiv.refl _) id (A.us x) (A.us x) _ _
    (List.map_id _) (List.map_id _) (fun y => Iso.refl (A.A x y)) (A.δ x) (A.δ x)
    (A.δ x) (A.δ x) HEq.rfl HEq.rfl (.ident _) (by
      change 𝟙 _ ≫ act 𝒮 Zₐ (fun y => 𝟙 (A.A x y)) (A.us x) ≫ A.δ x = A.δ x
      have h : act 𝒮 Zₐ (fun y => 𝟙 (A.A x y)) (A.us x) = 𝟙 _ :=
        occurrence_act_id (A.A x) (A.us x)
      rw [h, Category.id_comp, Category.id_comp])

section ReadAccumulated
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentAugData.reorderRead_accumulate_hom (A : OrderedDependentAugData I)
    {xs : List A.X} {us : A.X → List A.U}
    (e : AddressOrder A.X A.xs xs) (d : ∀ x, AddressOrder A.U (A.us x) (us x)) :
    ((A.reorderRead e d).accumulate R L J NL hl).hom =
      (A.accumulatedReorderIso e d R L hl hr J N NL).hom := by
  apply AugHom.ext
  let B := A.reorder e d
  let F := dependentLabels (T:=T) A.V A.A
  let q := A.reorderRead e d
  have lhs := q.accumulate_trace R L J NL hl id id Function.injective_id Function.injective_id
    (fun _ => rfl) F F (fun _ => rfl) (fun _ => rfl) (fun z => 𝟙 (F z))
    (fun z => heq_of_eq (T.map_id (A.V z.1) (A.A z.1 z.2)))
  have rhs := wordReindex_trace F F (dependentOrder e d) (dependentWord_nodup A.xs_unique A.us_unique)
    (dependentWord_nodup B.xs_unique B.us_unique) (fun z => Iso.refl (F z))
  exact RawSingletonTrace.eq lhs rhs (fun _ => rfl)

end ReadAccumulated

namespace DependentFubiniTree

/-- One order chart at each parent and continuation word at each leaf.
Internal nullaries are unchanged, not mistaken for empty families. -/
inductive AdditivePresentation : DependentFubiniTree I → DependentFubiniTree I → Type (max (u+1) v) where
  | unit : AdditivePresentation .unit .unit
  | leaf (A : OrderedDependentAugData I) {xs : List A.X} {us : A.X → List A.U}
      (e : AddressOrder A.X A.xs xs) (d : ∀ x, AddressOrder A.U (A.us x) (us x)) :
      AdditivePresentation (.leaf A) (.leaf (A.reorder e d))
  | fork {a b c d : DependentFubiniTree I} (e : AdditivePresentation a b) (f : AdditivePresentation c d) :
      AdditivePresentation (.fork a c) (.fork b d)

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
noncomputable def AdditivePresentation.jointRead {a b : DependentFubiniTree I} (p : AdditivePresentation a b) :
    OrderedDependentAugData.ReadComparison (a.jointInput R L J) (b.jointInput R L J) :=
  match p with
  | .unit => OrderedDependentAugData.identRead _
  | .leaf A e d => A.reorderRead e d
  | .fork e f => (e.jointRead).product R L J NR NL hl hr f.jointRead

set_option backward.isDefEq.respectTransparency false in
noncomputable def AdditivePresentation.separateIso {a b : DependentFubiniTree I} (p : AdditivePresentation a b) :
    NativeAugmentedIso (a.separate R L J) (b.separate R L J) :=
  match p with
  | .unit => NativeAugmentedIso.ident _
  | .leaf A e d => (A.reorderRead e d).accumulate R L J NL hl
  | .fork e f => independentAugIso R L (J.ρ I) N NR NL hl hr e.separateIso f.separateIso

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
theorem AdditivePresentation.comparison_natural {a b : DependentFubiniTree I} (p : AdditivePresentation a b) :
    (p.separateIso R L J N NR NL hl hr).hom.comp (b.comparison R L J N NR NL hl hr m mi h j unit_middle).hom =
      (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom.comp
        ((p.jointRead R L J NR NL hl hr).accumulate R L J NL hl).hom := by
  induction p with
  | unit =>
    let e := dependentUnitFubini R L hl hr J
    let q := ((OrderedDependentAugData.unit I).identRead.accumulate R L J NL hl).hom
    have t : q.comp e.inv = e.inv := by
      exact (AugHom.terminal _).trans (AugHom.terminal _).symm
    have r := congrArg (fun x => x.comp e.hom) t
    rw [AugHom.comp_assoc, e.inv_hom, AugHom.comp_ident] at r
    change (AugHom.ident _).comp e.hom = e.hom.comp q
    rw [r, AugHom.ident_comp, AugHom.comp_ident]
  | leaf A e d =>
    simp only [AdditivePresentation.separateIso, AdditivePresentation.jointRead, comparison,
      NativeAugmentedIso.ident]
    exact (AugHom.comp_ident _).trans (AugHom.ident_comp _).symm
  | fork e f he hf =>
    exact comparison_fork_congr R L J N NR NL hl hr m mi h j unit_middle _ _ _ _ he hf

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
