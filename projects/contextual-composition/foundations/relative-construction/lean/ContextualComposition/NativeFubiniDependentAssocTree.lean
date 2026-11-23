module
public import ContextualComposition.NativeFubiniReadPath
public import ContextualComposition.NativeFubiniDependentAssoc
@[expose] public section

/-! Actual mixed dependent associativity for arbitrary
independent binary trees of ragged three-level inputs. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {I : C} {T : Bi (coeff (C:=C))}
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
variable [IsIso (J.ρ I)]

section Unit
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

def OrderedDependentThirdData.unit (I : C) :
    OrderedDependentThirdData (OrderedDependentAugData.unit I) where
  W := PUnit.{u+1}
  eqW := inferInstance
  ws _ _ := [PUnit.unit]
  D _ _ _ := I
  unique _ _ _ _ := by simp
  γ _ _ := (ρ_ I).hom

local notation "A₀" => OrderedDependentAugData.unit I
local notation "D₀" => OrderedDependentThirdData.unit I

set_option backward.isDefEq.respectTransparency false in
include hl hr in
noncomputable def OrderedDependentThirdData.unitParentRead :
    WordAugReadComparison (A₀).V ((D₀).leftData R L J).V (A₀).xs ((D₀).leftData R L J).xs
      (A₀).ε ((D₀).leftData R L J).ε := by
  let e : PUnit.{u+1} ≃ PUnit.{u+1} × PUnit.{u+1} :=
    { toFun := fun x => (x,x)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun _ => Subsingleton.elim _ _ }
  let φ := (asIso (J.ρ I)).symm
  have hm : (A₀).xs.map e = ((D₀).leftData R L J).xs := rfl
  refine WordAugReadComparison.ofOrderPreserving e hm (fun _ => φ) _ _ ?_
  change (φ.hom ⊗ₘ 𝟙 Zₐ) ≫ eqToHom _ ≫
    ((D₀).leftData R L J).ε = (ρ_ I).hom
  have ha : ((D₀).leftData R L J).ε = (ρ_ (T.obj I I)).hom ≫ J.ρ I :=
    dependentUnit_augCell R L hl hr J
  rw [ha, eqToHom_refl, Category.id_comp, tensorHom_id, rightUnitor_naturality_assoc]
  change (ρ_ I).hom ≫ (φ.hom ≫ φ.inv) = (ρ_ I).hom
  rw [φ.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
include hl hr in
noncomputable def OrderedDependentThirdData.unitLeftRead :
    OrderedDependentAugData.ReadComparison A₀ ((D₀).leftData R L J) where
  parent := OrderedDependentThirdData.unitParentRead R L J hl hr
  child _ := wordIdentityRead (fun _ : PUnit.{u+1} => I)
    [PUnit.unit] (ρ_ I).hom

set_option backward.isDefEq.respectTransparency false in
include hl hr in
noncomputable def OrderedDependentThirdData.unitRightRead :
    OrderedDependentAugData.ReadComparison A₀ ((D₀).rightData R L J) where
  parent := wordIdentityRead (A₀).V (A₀).xs (A₀).ε
  child x := by
    cases x
    exact OrderedDependentThirdData.unitParentRead R L J hl hr

end Unit

inductive DependentThirdTree (I : C) where
  | unit
  | leaf (A : OrderedDependentAugData I) (D : OrderedDependentThirdData A)
  | fork (l r : DependentThirdTree I)

namespace DependentThirdTree
local notation "prd" => OrderedDependentAugData.product R L J
local notation "acc" => OrderedDependentAugData.accumulate R L J
local notation "inp" => DependentFubiniTree.jointInput R L J
local notation "sep" => DependentFubiniTree.separate R L J
local notation "lft" => OrderedDependentThirdData.leftData R L J
local notation "rgt" => OrderedDependentThirdData.rightData R L J
local notation "ph" => DependentFubiniTree.comparison R L J N NR NL hl hr m mi h j unit_middle
local notation "bi" => OrderedDependentAugData.binaryFubini R L J N NR NL hl hr m mi h j unit_middle
local notation "nm" => independentAugMap R L (J.ρ I) N NR NL hl hr
local notation "ni" => independentAugIso R L (J.ρ I) N NR NL hl hr
local notation "rc" => OrderedDependentAugData.ReadComparison.accumulate R L J NL hl
local notation "ri" => OrderedReadPath.iso R L J NL hl
local notation "da" => fun D => OrderedDependentThirdData.associator R L J D P NL Q U hl ι
local notation "pw" => OrderedDependentThirdData.parentFubiniComparison R L J N NR NL m mi h j unit_middle hl hr
local notation "tw" => OrderedDependentThirdData.tailFubiniComparison R L J N NR NL m mi h j unit_middle hl hr

def base : DependentThirdTree I → OrderedDependentAugData I
  | .unit => OrderedDependentAugData.unit I
  | .leaf A _ => A
  | .fork l r => prd (base l) (base r)

def third : (t : DependentThirdTree I) → OrderedDependentThirdData (base R L J t)
  | .unit => OrderedDependentThirdData.unit I
  | .leaf _ D => D
  | .fork l r => OrderedDependentThirdData.product R L J (third l) (third r)

def leftTree : DependentThirdTree I → DependentFubiniTree I
  | .unit => .unit
  | .leaf _ D => .leaf (lft D)
  | .fork l r => .fork (leftTree l) (leftTree r)

def rightTree : DependentThirdTree I → DependentFubiniTree I
  | .unit => .unit
  | .leaf _ D => .leaf (rgt D)
  | .fork l r => .fork (rightTree l) (rightTree r)

local notation "LT" => leftTree R L J
local notation "RT" => rightTree R L J
local notation "D" => third R L J

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateAssoc : (t : DependentThirdTree I) → NativeAugmentedIso (sep (LT t)) (sep (RT t))
  | .unit => NativeAugmentedIso.ident _
  | .leaf _ d => da d
  | .fork l r => ni (separateAssoc l) (separateAssoc r)

noncomputable def leftPath : (t : DependentThirdTree I) → OrderedReadPath (inp (LT t)) (lft (D t))
  | .unit => .cons (OrderedDependentThirdData.unitLeftRead R L J hl hr) (.nil (lft (D .unit)))
  | .leaf _ d => .nil (lft d)
  | .fork l r => ((leftPath l).product R L J NR NL hl hr (leftPath r)).append
      (.cons (pw (D l) (D r)) (.nil (lft (OrderedDependentThirdData.product R L J (D l) (D r)))))

noncomputable def rightPath : (t : DependentThirdTree I) → OrderedReadPath (inp (RT t)) (rgt (D t))
  | .unit => .cons (OrderedDependentThirdData.unitRightRead R L J hl hr) (.nil (rgt (D .unit)))
  | .leaf _ d => .nil (rgt d)
  | .fork l r => ((rightPath l).product R L J NR NL hl hr (rightPath r)).append
      (.cons (tw (D l) (D r)) (.nil (rgt (OrderedDependentThirdData.product R L J (D l) (D r)))))

local notation "lp" => leftPath R L J N NR NL hl hr m mi h j unit_middle
local notation "rp" => rightPath R L J N NR NL hl hr m mi h j unit_middle

noncomputable def leftMixed (t : DependentThirdTree I) :
    NativeAugmentedIso (sep (LT t)) (acc (lft (D t))) :=
  (ph (LT t)).trans (ri (lp t))

noncomputable def rightMixed (t : DependentThirdTree I) :
    NativeAugmentedIso (sep (RT t)) (acc (rgt (D t))) :=
  (ph (RT t)).trans (ri (rp t))

local notation "lm" => leftMixed R L J N NR NL hl hr m mi h j unit_middle
local notation "rm" => rightMixed R L J N NR NL hl hr m mi h j unit_middle
local notation "sa" => separateAssoc R L J P N NR NL Q U hl hr ι

set_option backward.isDefEq.respectTransparency false in
theorem leftMixed_fork (l r : DependentThirdTree I) :
    (lm (.fork l r)).hom =
      ((nm (lm l).hom (lm r).hom).comp (bi (lft (D l)) (lft (D r))).hom).comp
        (rc (pw (D l) (D r))).hom := by
  have e := OrderedReadPath.product_fubini R L J N NR NL hl hr m mi h j unit_middle (lp l) (lp r)
  change ((nm (ph (LT l)).hom (ph (LT r)).hom).comp
      (bi (inp (LT l)) (inp (LT r))).hom).comp
      (ri (((lp l).product R L J NR NL hl hr (lp r)).append
        (.cons (pw (D l) (D r)) (.nil _)))).hom = _
  rw [OrderedReadPath.append_hom]
  change _ = ((nm ((ph (LT l)).hom.comp (ri (lp l)).hom)
       ((ph (LT r)).hom.comp (ri (lp r)).hom)).comp (bi (lft (D l)) (lft (D r))).hom).comp _
  rw [independentAugMap_comp]
  have e' := congrArg (fun p => p.comp (rc (pw (D l) (D r))).hom) e
  have hz : (ri (.cons (pw (D l) (D r)) (.nil (lft (OrderedDependentThirdData.product R L J (D l) (D r)))))).hom =
      (rc (pw (D l) (D r))).hom := AugHom.comp_ident _
  rw [hz]
  simp only [AugHom.comp_assoc] at e' ⊢
  rw [e']

set_option backward.isDefEq.respectTransparency false in
theorem rightMixed_fork (l r : DependentThirdTree I) :
    (rm (.fork l r)).hom =
      ((nm (rm l).hom (rm r).hom).comp (bi (rgt (D l)) (rgt (D r))).hom).comp
        (rc (tw (D l) (D r))).hom := by
  have e := OrderedReadPath.product_fubini R L J N NR NL hl hr m mi h j unit_middle (rp l) (rp r)
  change ((nm (ph (RT l)).hom (ph (RT r)).hom).comp
      (bi (inp (RT l)) (inp (RT r))).hom).comp
      (ri (((rp l).product R L J NR NL hl hr (rp r)).append
        (.cons (tw (D l) (D r)) (.nil _)))).hom = _
  rw [OrderedReadPath.append_hom]
  change _ = ((nm ((ph (RT l)).hom.comp (ri (rp l)).hom)
       ((ph (RT r)).hom.comp (ri (rp r)).hom)).comp (bi (rgt (D l)) (rgt (D r))).hom).comp _
  rw [independentAugMap_comp]
  have e' := congrArg (fun p => p.comp (rc (tw (D l) (D r))).hom) e
  have hz : (ri (.cons (tw (D l) (D r)) (.nil (rgt (OrderedDependentThirdData.product R L J (D l) (D r)))))).hom =
      (rc (tw (D l) (D r))).hom := AugHom.comp_ident _
  rw [hz]
  simp only [AugHom.comp_assoc] at e' ⊢
  rw [e']

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4700000 in
/-- The full mixed square for every finite independent tree.
The horizontal maps are original Fubini, followed by explicit
parent-only or tail-only ordered whiskering on the joint side. -/
theorem mixed_coherent (t : DependentThirdTree I) (law : MedialDependentAssoc P m) :
    (lm t).hom.comp (da (D t)).hom = (sa t).hom.comp (rm t).hom := by
  induction t with
  | unit =>
    let f := (lm .unit).hom.comp (da (D .unit)).hom
    let e := rm .unit
    have hf : f.comp e.inv = e.hom.comp e.inv :=
      (AugHom.terminal _).trans (AugHom.terminal _).symm
    have ht := congrArg (fun y => y.comp e.hom) hf
    have he : f = e.hom := by
      simpa only [AugHom.comp_assoc, e.inv_hom, AugHom.comp_ident] using ht
    change f = (AugHom.ident _).comp e.hom
    rw [AugHom.ident_comp]
    exact he
  | leaf A d =>
    change ((AugHom.ident _).comp (AugHom.ident _)).comp (da d).hom =
      (da d).hom.comp ((AugHom.ident _).comp (AugHom.ident _))
    simp only [AugHom.ident_comp, AugHom.comp_ident]
  | fork l r ihL ihR =>
    rw [leftMixed_fork, rightMixed_fork]
    have b := OrderedDependentThirdData.actual_fubini_dependent_assoc R L J P N NR NL Q U hl hr
      ι m mi h j unit_middle (D l) (D r) law
    change (((bi (lft (D l)) (lft (D r))).hom.comp (rc (pw (D l) (D r))).hom).comp
      (da (OrderedDependentThirdData.product R L J (D l) (D r))).hom) =
      (((nm (da (D l)).hom (da (D r)).hom).comp (bi (rgt (D l)) (rgt (D r))).hom).comp
        (rc (tw (D l) (D r))).hom) at b
    have ts := congrArg₂ (fun x y => nm x y) ihL ihR
    rw [independentAugMap_comp, independentAugMap_comp] at ts
    change (((nm (lm l).hom (lm r).hom).comp (bi (lft (D l)) (lft (D r))).hom).comp
        (rc (pw (D l) (D r))).hom).comp (da (OrderedDependentThirdData.product R L J (D l) (D r))).hom =
      (nm (sa l).hom (sa r).hom).comp (((nm (rm l).hom (rm r).hom).comp
        (bi (rgt (D l)) (rgt (D r))).hom).comp (rc (tw (D l) (D r))).hom)
    rw [AugHom.comp_assoc (nm (lm l).hom (lm r).hom), AugHom.comp_assoc (nm (lm l).hom (lm r).hom),
      b]
    simp only [AugHom.comp_assoc]
    have tt := congrArg (fun z => z.comp ((bi (rgt (D l)) (rgt (D r))).hom.comp
      (rc (tw (D l) (D r))).hom)) ts
    simpa only [AugHom.comp_assoc] using tt

end DependentThirdTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
