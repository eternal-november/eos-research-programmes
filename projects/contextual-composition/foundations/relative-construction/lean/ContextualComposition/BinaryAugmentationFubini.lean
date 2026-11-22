module
public import ContextualComposition.RawBinaryChart
@[expose] public section
/-! The augmentation endpoint of binary coefficient Fubini. The only
augmentation data on the parent objects are the two global maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z I : C}
set_option backward.isDefEq.respectTransparency false
variable (M : AddCross S Z) (R : Gather S T Z) (L : LeftGather S T Z)
variable (N : GridBinary M R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (J : UnitCompat R I) (m : Middle T I)
def unitCollapse : K.Hom (T.obj (T.obj I I) (T.obj I I)) I :=
  K.seq (T.map (J.ρ I) (J.ρ I)) (J.ρ I)
variable {X Y : Type u} (xs : List X) (ys : List Y)
variable (V : X → C) (W : Y → C) (B : Input X C) (D : Input Y C)
variable (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) B x) I)
variable (δ' : ∀ y, K.Hom (inner (S:=S) (Z:=Z) D y) I)
variable (ε : K.Hom (fold S Z V xs) I) (ε' : K.Hom (fold S Z W ys) I)
include N NR NL in
/-- One binary augmentation calculation from the occurrence-first chart.
The continuation augmentations stay inside their chosen parent branches;
the outer augmentations are actual maps of complete outer sums. -/
theorem binary_augmentation_chart (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : K.seq (m.cell I I I I) (unitCollapse R J) = unitCollapse R J) :
    K.seq (occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys B.terms D.terms)
      (K.seq (T.map (augmentation L J V B xs δ ε) (augmentation L J W D ys δ' ε')) (J.ρ I)) =
    K.seq (exchangeInner (T:=T) M (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys B.terms D.terms)
      (K.seq (jointNative R L xs ys V W B D δ δ' ε ε' m) (unitCollapse R J)) := by
  have k := binary_native_routes M R L N xs ys NR NL V W B D δ δ' ε ε' m h j
  have g := congrArg (fun f => K.seq f (unitCollapse R J)) k
  simp only [K.assoc, unit_middle] at g
  unfold unitCollapse at g
  rw [← K.assoc (T.map (dep R _ _ _ _ _ _) (dep R _ _ _ _ _ _)), ← T.map_seq,
    augmentation_normal L J, augmentation_normal L J] at g
  exact g

section JointUnit
variable {X Y : Type u} (xs : List X) (ys : List Y) (A : X → Y → C)
def rectKeep (z : C) :=
  K.seq (act S Z (fun x => (Lin.right R z).collect (A x) ys) xs)
    ((Lin.right R z).collect (fun x => fold S Z (A x) ys) xs)

theorem rectKeep_post {a b : C} (q : K.Hom a b) :
    K.seq (rectKeep R xs ys A a) (T.map (K.id _) q) =
      K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => T.map (K.id (A x y)) q))
        (rectKeep R xs ys A b) := by
  unfold rectKeep actRect
  rw [K.assoc, (rightLinear R q).collect, ← K.assoc, act_seq]
  simp only [(rightLinear R q).collect]
  rw [← act_seq, K.assoc]

theorem rectKeep_unit :
    K.seq (rectKeep R xs ys A I) (J.ρ _) =
      actRect (S:=S) (Z:=Z) xs ys (fun x y => J.ρ (A x y)) := by
  unfold rectKeep actRect
  simp only [collect_right_eq]
  rw [K.assoc, gather_unit J, act_seq]
  simp only [gather_unit J]

/-- Move a single continuation collapse across the actual whole parent
map. Zero fibres are handled inside the two gathering diagrams. -/
theorem rectKeep_global {b : C} (δ : K.Hom b I)
    (ε : K.Hom (fold S Z (fun x => fold S Z (A x) ys) xs) I) :
    K.seq (rectKeep R xs ys A b) (K.seq (T.map ε δ) (J.ρ I)) =
      K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y =>
        K.seq (T.map (K.id (A x y)) δ) (J.ρ (A x y)))) ε := by
  have fac : T.map ε δ = K.seq (T.map (K.id _) δ) (T.map ε (K.id I)) := by
    rw [← T.map_seq, K.id_seq, K.seq_id]
  rw [fac, K.assoc, J.natural, ← K.assoc (rectKeep _ _ _ _ _), rectKeep_post R xs ys A]
  simp only [K.assoc]
  rw [← K.assoc (rectKeep _ _ _ _ _), rectKeep_unit R J xs ys A, ← K.assoc, actRect_seq]
end JointUnit

section ActualJoint
def jointContAug (x : X) (y : Y) :=
  K.seq (independentCell R L id id (B.terms x) (D.terms y) (δ x) (δ' y)) (J.ρ I)
def jointParentAug :=
  K.seq (independentCell R L V W xs ys ε ε') (J.ρ I)
def jointAugRow (x : X) (y : Y) :=
  let A := T.obj (V x) (W y)
  let bs := B.terms x
  let ds := D.terms y
  K.seq (act S Z (fun v => (Lin.left L A).collect (T.obj v) ds) bs)
    (K.seq ((Lin.left L A).collect (fun v => fold S Z (T.obj v) ds) bs)
      (K.seq (T.map (K.id A) (jointContAug R L J B D δ δ' x y)) (J.ρ A)))

/-- The joint augmentation is built independently: actual independent
continuation augmentations, continuation-before-parent unit removal,
then the independent tensor of the two global parent augmentations. -/
def actualJointAug :=
  K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y =>
      actRect (S:=S) (Z:=Z) (B.terms x) (D.terms y) (fun u v => m.cell (V x) u (W y) v)))
    (K.seq (actRect (S:=S) (Z:=Z) xs ys (jointAugRow R L J V W B D δ δ'))
      (jointParentAug R L J xs ys V W ε ε'))

theorem joint_aug_reduction :
    K.seq (jointNative R L xs ys V W B D δ δ' ε ε' m) (unitCollapse R J) =
      actualJointAug R L J m xs ys V W B D δ δ' ε ε' := by
  unfold jointNative jointOuterCell unitCollapse actualJointAug
  simp only [K.assoc]
  rw [← K.assoc (T.map (independentCell _ _ _ _ _ _ _ _) (K.id _)), ← T.map_seq, K.id_seq]
  rw [← K.assoc (act S Z (fun x => (Lin.right R (T.obj I I)).collect (fun y => T.obj (V x) (W y)) ys) xs)]
  change K.seq _ (K.seq _ (K.seq (rectKeep R xs ys (fun x y => T.obj (V x) (W y)) (T.obj I I))
    (K.seq (T.map (jointParentAug R L J xs ys V W ε ε') (J.ρ I)) (J.ρ I)))) = _
  rw [rectKeep_global R J xs ys, ← K.assoc (actRect xs ys (jointInnerCell R L V W B D δ δ')), actRect_seq]
  congr 1
  congr 1
  congr 1
  funext x y
  unfold jointInnerCell jointAugRow jointContAug
  simp only [K.assoc]
  rw [← K.assoc (T.map (K.id _) (independentCell _ _ _ _ _ _ _ _)), ← T.map_seq, K.id_seq]

include N NR NL in
/-- Binary Fubini preserves the actual global augmentation of the two
accumulations. This equality is on the chosen occurrence-first chart;
there are two whole parent augmentations, not component augmentations. -/
theorem binary_global_augmentation (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : K.seq (m.cell I I I I) (unitCollapse R J) = unitCollapse R J) :
    K.seq (occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys B.terms D.terms)
      (K.seq (T.map (augmentation L J V B xs δ ε) (augmentation L J W D ys δ' ε')) (J.ρ I)) =
    K.seq (exchangeInner (T:=T) M (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys B.terms D.terms)
      (actualJointAug R L J m xs ys V W B D δ δ' ε ε') := by
  rw [← joint_aug_reduction R L J m xs ys]
  exact binary_augmentation_chart M R L N NR NL J m xs ys V W B D δ δ' ε ε' h j unit_middle
end ActualJoint
end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C] in
theorem unit_middle_collapse :
    tensorμ (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C) ≫
      ((ρ_ (𝟙_ C)).hom ⊗ₘ (ρ_ (𝟙_ C)).hom) ≫ (ρ_ (𝟙_ C)).hom =
    ((ρ_ (𝟙_ C)).hom ⊗ₘ (ρ_ (𝟙_ C)).hom) ≫ (ρ_ (𝟙_ C)).hom := by
  have e := tensor_left_unitality (𝟙_ C) (𝟙_ C)
  have g := congrArg (fun f => ((λ_ (𝟙_ C)).hom ▷ (𝟙_ C ⊗ 𝟙_ C)) ≫ f ≫ (ρ_ (𝟙_ C)).hom) e
  simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp] at g
  calc
    _ = ((λ_ (𝟙_ C)).hom ▷ (𝟙_ C ⊗ 𝟙_ C)) ≫ (λ_ (𝟙_ C ⊗ 𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).hom := by
      calc
        _ = tensorμ (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C) ≫
          ((λ_ (𝟙_ C)).hom ⊗ₘ (λ_ (𝟙_ C)).hom) ≫ (ρ_ (𝟙_ C)).hom := by monoidal
        _ = _ := g.symm
    _ = _ := by monoidal

variable [BraidedCategory C] in
theorem standard_unit_middle {S : Bi (coeff (C:=C))} {Z : C}
    (R : Gather S (binary (Binary.ofMonoidal (C:=C))) Z) (J : UnitCompat R (𝟙_ C))
    (h : J.ρ (𝟙_ C) = (ρ_ (𝟙_ C)).hom) :
    (additiveMiddle (Additive.ofBraided (C:=C))).cell (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C) ≫
      unitCollapse R J = unitCollapse R J := by
  unfold unitCollapse
  change tensorμ (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C) ≫ ((J.ρ (𝟙_ C) ⊗ₘ J.ρ (𝟙_ C)) ≫ J.ρ (𝟙_ C)) =
    (J.ρ (𝟙_ C) ⊗ₘ J.ρ (𝟙_ C)) ≫ J.ρ (𝟙_ C)
  rw [h]
  exact unit_middle_collapse

section Flat
variable [SymmetricCategory C]
local notation "𝒮" => binary Binary.ofMonoidal
variable {T : Bi (coeff (C:=C))}
variable (R : Gather 𝒮 T (𝟙_ C)) (L : LeftGather 𝒮 T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {I : C} (J : UnitCompat R I) (m : Middle T I)
variable {X Y : Type u} (xs : List X) (ys : List Y)
variable (V : X → C) (W : Y → C) (B : Input X C) (D : Input Y C)
variable (δ : ∀ x : X, inner (S:=𝒮) (Z:=𝟙_ C) B x ⟶ I)
variable (δ' : ∀ y : Y, inner (S:=𝒮) (Z:=𝟙_ C) D y ⟶ I)
variable (ε : fold 𝒮 (𝟙_ C) V xs ⟶ I) (ε' : fold 𝒮 (𝟙_ C) W ys ⟶ I)
local notation "Av" => fun x => T.obj (V x)
local notation "Bv" => fun y => T.obj (W y)
def separateGlobalAug :=
  occurrenceFirst R L Av Bv xs ys B.terms D.terms ≫
    T.map (augmentation L J V B xs δ ε) (augmentation L J W D ys δ' ε') ≫ J.ρ I

include N NR NL in
/-- Equality of the two global augmentation arrows from the canonical
flat binary occurrence word, with separately constructed chart maps. -/
theorem binary_global_augmentation_flat (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) :
    compressTree (quadLabels (T:=T) Av Bv) (fourOccurrenceExpr xs ys B.terms D.terms) ≫
      transportSource (K:=coeff (C:=C)) (occurrence_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys B.terms D.terms)
        (separateGlobalAug R L J xs ys V W B D δ δ' ε ε') =
    flatCircuit (quadLabels (T:=T) Av Bv) (fourExchangeChart xs ys B.terms D.terms) (𝟙_ C) ≫
      compressTree (quadLabels (T:=T) Av Bv) (fourJointExpr xs ys B.terms D.terms) ≫
      transportSource (K:=coeff (C:=C)) (joint_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys B.terms D.terms)
        (actualJointAug R L J m xs ys V W B D δ δ' ε ε') := by
  rw [← Category.assoc (flatCircuit _ _ _), independent_std_charts, Category.assoc]
  have e := transport_paste (occurrence_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys B.terms D.terms)
    (joint_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys B.terms D.terms)
    (fourExchangeChart_eval (symmetricCross (C:=C)) (T:=T) Av Bv xs ys B.terms D.terms)
    (actualJointAug R L J m xs ys V W B D δ δ' ε ε')
  have k := binary_global_augmentation (symmetricCross (C:=C)) R L N NR NL J m
    xs ys V W B D δ δ' ε ε' h j unit_middle
  let C₀ := compressTree (quadLabels (T:=T) Av Bv) (fourOccurrenceExpr xs ys B.terms D.terms)
  calc
    _ = C₀ ≫ transportSource (K:=coeff (C:=C)) (occurrence_expr_obj Av Bv xs ys B.terms D.terms)
      (exchangeInner (T:=T) (symmetricCross (C:=C)) Av Bv xs ys B.terms D.terms ≫
        actualJointAug R L J m xs ys V W B D δ δ' ε ε') :=
      congrArg (fun f => C₀ ≫ transportSource (K:=coeff (C:=C)) _ f) k
    _ = _ := congrArg (fun f => C₀ ≫ f) e.symm

section Raw
variable {U Yb : Type u} (us : X → List U) (vs : Y → List Yb)
variable (A : X → U → C) (E : Y → Yb → C)
variable (β : ∀ x : X, inner (S:=𝒮) (Z:=𝟙_ C) (indexInput A us) x ⟶ I)
variable (θ : ∀ y : Y, inner (S:=𝒮) (Z:=𝟙_ C) (indexInput E vs) y ⟶ I)
noncomputable def rawSeparateAug :=
  compressTree (quadLabels (T:=T) Av Bv)
    (fourOccurrenceExpr xs ys (indexInput A us).terms (indexInput E vs).terms) ≫
    transportSource (K:=coeff (C:=C))
      (occurrence_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys (indexInput A us).terms (indexInput E vs).terms)
      (separateGlobalAug R L J xs ys V W (indexInput A us) (indexInput E vs) β θ ε ε')
noncomputable def rawJointAug :=
  flatCircuit (quadLabels (T:=T) Av Bv)
    (fourExchangeChart xs ys (indexInput A us).terms (indexInput E vs).terms) (𝟙_ C) ≫
    compressTree (quadLabels (T:=T) Av Bv)
      (fourJointExpr xs ys (indexInput A us).terms (indexInput E vs).terms) ≫
    transportSource (K:=coeff (C:=C))
      (joint_expr_obj (S:=𝒮) (Z:=𝟙_ C) (T:=T) Av Bv xs ys (indexInput A us).terms (indexInput E vs).terms)
      (actualJointAug R L J m xs ys V W (indexInput A us) (indexInput E vs) β θ ε ε')

include N NR NL in
theorem raw_binary_global_augmentation (h : MedialLinear m R L) (j : MedialInner m R L)
    (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) :
    rawEntry (T:=T) xs ys us vs V W A E ≫ rawSeparateAug R L J xs ys V W ε ε' us vs A E β θ =
    rawEntry (T:=T) xs ys us vs V W A E ≫ rawJointAug R L J m xs ys V W ε ε' us vs A E β θ := by
  exact congrArg (fun f => rawEntry (T:=T) xs ys us vs V W A E ≫ f)
    (binary_global_augmentation_flat R L N NR NL J m xs ys V W (indexInput A us) (indexInput E vs)
      β θ ε ε' h j unit_middle)
end Raw
end Flat
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
