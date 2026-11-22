module
public import ContextualComposition.NativeAttachParent

@[expose] public section
/-! Actual native parent-coefficient change after a continuation gather. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open Functor.LaxMonoidal
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)

variable (T : Bi (coeff (C:=C))) {a b : C}

/-- Actual multiplicative change of the fixed parent parameter. -/
def leftFactorChange (p : a ⟶ b) : leftFactor T a ⟶ leftFactor T b where
  app x := T.map p (𝟙 x)
  naturality x y f := by
    change T.map (𝟙 a) f ≫ T.map p (𝟙 y) = T.map p (𝟙 x) ≫ T.map (𝟙 b) f
    have e := (T.map_seq (𝟙 a) p f (𝟙 y)).symm.trans (by
      simpa only [coeff, Category.id_comp, Category.comp_id] using T.map_seq p (𝟙 b) (𝟙 x) f)
    exact e

variable [(leftFactor T a).LaxBraided] [(leftFactor T b).LaxBraided]
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

set_option backward.isDefEq.respectTransparency false in
theorem leftFactorChange_linear (p : a ⟶ b) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) (hb : SameLeftGather T b L) :
    LinSquare (linearFunctor (leftFactor T a)) (linearFunctor (leftFactor T b))
      (leftFactorChange T p).app := by
  constructor
  · change ε (leftFactor T a) ≫ T.map p (𝟙 (𝟙_ C)) = ε (leftFactor T b)
    rw [ha.1, hb.1]
    exact (N.outer p).nil
  · intro x y
    change μ (leftFactor T a) x y ≫ T.map p (𝟙 (x ⊗ y)) =
      (T.map p (𝟙 x) ⊗ₘ T.map p (𝟙 y)) ≫ μ (leftFactor T b) x y
    rw [ha.2, hb.2]
    exact (N.outer p).cons x y


set_option backward.isDefEq.respectTransparency false in
theorem changeAugUnit_twice_ε {I J K : C} (A : Aug ℙ I) (p : I ⟶ J) (q : J ⟶ K) :
    (changeAugUnit (changeAugUnit A p) q).ε = (changeAugUnit A (p ≫ q)).ε := by
  change (A.ε.comp (pointwiseNative (fun _ : Fin 1 => p))).comp
    (pointwiseNative (fun _ : Fin 1 => q)) = _
  rw [Hom.comp_assoc]
  congr 1
  rw [native_post_pointwise]
  apply congrArg (Hom.mk (S:=ℙ) (A:=terminalShape I) (B:=terminalShape K) id)
  funext j
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- If the parent coefficient change commutes with the one target arrow
on the whole augmented continuation, it lifts to an actual augmented
pointwise map. The gather naturality, including its empty case, is
derived from the declared dependent left gather. -/
noncomputable def changeAttachedParent {I J : C} (A : Aug ℙ I)
    (p : a ⟶ b) (q : T.obj a I ⟶ J) (r : T.obj b I ⟶ J)
    (h : T.map p (𝟙 I) ≫ r = q) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) (hb : SameLeftGather T b L) :
    AugHom ℙ (attachParent T a A q) (attachParent T b A r) where
  native := pointwiseNative (fun i => T.map p (𝟙 (A.base.val i)))
  preserves := by
    let j := linearAugComparison (leftFactorChange T p) A (leftFactorChange_linear T L p N ha hb)
    let v := changeAugUnit_map j r
    change v.native.comp (changeAugUnit (linearAug (leftFactor T b) A) r).ε =
      (attachParent T a A q).ε
    rw [v.preserves]
    subst q
    exact changeAugUnit_twice_ε (linearAug (leftFactor T a) A) (T.map p (𝟙 I)) r

set_option backward.isDefEq.respectTransparency false in
theorem attachParent_change_natural {I J : C} {A B : Aug ℙ I}
    (u : AugHom ℙ A B) (p : a ⟶ b) (q : T.obj a I ⟶ J) (r : T.obj b I ⟶ J)
    (h : T.map p (𝟙 I) ≫ r = q) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) (hb : SameLeftGather T b L) :
    (attachParentMap T a u q).native.comp (changeAttachedParent T L B p q r h N ha hb).native =
      (changeAttachedParent T L A p q r h N ha hb).native.comp (attachParentMap T b u r).native :=
  linearNative_natural (leftFactorChange T p) u.native (leftFactorChange_linear T L p N ha hb)

set_option backward.isDefEq.respectTransparency false in
/-- Continuation first, parent coefficient change second: exactly the
existing left gather followed by the simultaneous multiplicative map. -/
theorem attachParent_then_change_cell {I J : C} {A B : Aug ℙ I}
    (u : AugHom ℙ A B) (p : a ⟶ b) (q : T.obj a I ⟶ J) (r : T.obj b I ⟶ J)
    (h : T.map p (𝟙 I) ≫ r = q) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) (hb : SameLeftGather T b L) (j : Fin B.base.n) :
    ((attachParentMap T a u q).comp (changeAttachedParent T L B p q r h N ha hb)).native.cell j =
      Lin.collect (Lin.left L a) A.base.val (fibreList u.native.addr j) ≫ T.map p (u.native.cell j) := by
  have e := native_post_pointwise (attachParentMap T a u q).native
    (fun i => T.map p (𝟙 (B.base.val i)))
  change Hom.mk (S:=ℙ) (A:=(attachParent T a A q).base) (B:=(attachParent T b B r).base) u.native.addr
    ((attachParentMap T a u q).comp (changeAttachedParent T L B p q r h N ha hb)).native.cell =
    Hom.mk (S:=ℙ) (A:=(attachParent T a A q).base) (B:=(attachParent T b B r).base) u.native.addr
      (fun i => (attachParentMap T a u q).native.cell i ≫ T.map p (𝟙 (B.base.val i))) at e
  injection e with ep ez
  have c := congrFun ez j
  refine c.trans ?_
  change (attachParentMap T a u q).native.cell j ≫ T.map p (𝟙 (B.base.val j)) = _
  rw [attachParent_exact_cell T a L u q ha, Category.assoc]
  congr 1
  have z := T.map_seq (𝟙 a) p (u.native.cell j) (𝟙 (B.base.val j))
  simpa only [coeff, Category.id_comp, Category.comp_id] using z.symm

theorem attachParent_change_aug_natural {I J : C} {A B : Aug ℙ I}
    (u : AugHom ℙ A B) (p : a ⟶ b) (q : T.obj a I ⟶ J) (r : T.obj b I ⟶ J)
    (h : T.map p (𝟙 I) ≫ r = q) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) (hb : SameLeftGather T b L) :
    (attachParentMap T a u q).comp (changeAttachedParent T L B p q r h N ha hb) =
      (changeAttachedParent T L A p q r h N ha hb).comp (attachParentMap T b u r) :=
  AugHom.ext (attachParent_change_natural T L u p q r h N ha hb)

set_option backward.isDefEq.respectTransparency false in
theorem attachParent_map_comp {I J : C} {A B D : Aug ℙ I}
    (u : AugHom ℙ A B) (v : AugHom ℙ B D) (q : T.obj a I ⟶ J) :
    attachParentMap T a (u.comp v) q =
      (attachParentMap T a u q).comp (attachParentMap T a v q) := by
  apply AugHom.ext
  exact linearNativeMap_comp (leftFactor T a) u.native v.native

set_option backward.isDefEq.respectTransparency false in
theorem attachParent_map_ident {I J : C} (A : Aug ℙ I) (q : T.obj a I ⟶ J) :
    attachParentMap T a (AugHom.ident A) q = AugHom.ident (attachParent T a A q) := by
  apply AugHom.ext
  exact linearNativeMap_ident (leftFactor T a) A.base

set_option backward.isDefEq.respectTransparency false in
theorem changeAttachedParent_comp {c : C} [(leftFactor T c).LaxBraided]
    {I J : C} (A : Aug ℙ I) (p : a ⟶ b) (o : b ⟶ c)
    (q : T.obj a I ⟶ J) (r : T.obj b I ⟶ J) (s : T.obj c I ⟶ J)
    (hp : T.map p (𝟙 I) ≫ r = q) (ho : T.map o (𝟙 I) ≫ s = r)
    (hpo : T.map (p ≫ o) (𝟙 I) ≫ s = q) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) (hb : SameLeftGather T b L) (hc : SameLeftGather T c L) :
    (changeAttachedParent T L A p q r hp N ha hb).comp
      (changeAttachedParent T L A o r s ho N hb hc) =
      changeAttachedParent T L A (p ≫ o) q s hpo N ha hc := by
  apply AugHom.ext
  change (pointwiseNative (fun i => T.map p (𝟙 (A.base.val i)))).comp
    (pointwiseNative (fun i => T.map o (𝟙 (A.base.val i)))) =
    pointwiseNative (fun i => T.map (p ≫ o) (𝟙 (A.base.val i)))
  rw [native_post_pointwise]
  apply congrArg (Hom.mk (S:=ℙ) (A:=(attachParent T a A q).base) (B:=(attachParent T c A s).base) id)
  funext i
  change (standardPushSingle (fun k => T.obj a (A.base.val k)) i ≫ T.map p (𝟙 (A.base.val i))) ≫
      T.map o (𝟙 (A.base.val i)) =
    standardPushSingle (fun k => T.obj a (A.base.val k)) i ≫ T.map (p ≫ o) (𝟙 (A.base.val i))
  rw [Category.assoc]
  congr 1
  simpa only [coeff, Category.id_comp] using (T.map_seq p o (𝟙 (A.base.val i)) (𝟙 (A.base.val i))).symm

set_option backward.isDefEq.respectTransparency false in
theorem changeAttachedParent_ident {I J : C} (A : Aug ℙ I) (q : T.obj a I ⟶ J)
    (h : T.map (𝟙 a) (𝟙 I) ≫ q = q) (N : GatherLeftNat L)
    (ha : SameLeftGather T a L) :
    changeAttachedParent T L A (𝟙 a) q q h N ha ha =
      AugHom.ident (attachParent T a A q) := by
  apply AugHom.ext
  apply congrArg (Hom.mk (S:=ℙ) (A:=(attachParent T a A q).base) (B:=(attachParent T a A q).base) id)
  funext i
  change standardPushSingle (fun k => T.obj a (A.base.val k)) i ≫ T.map (𝟙 a) (𝟙 (A.base.val i)) =
    standardPushSingle (fun k => T.obj a (A.base.val k)) i
  have h' : T.map (𝟙 a) (𝟙 (A.base.val i)) = 𝟙 (T.obj a (A.base.val i)) := T.map_id a (A.base.val i)
  rw [h', Category.comp_id]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
