module
public import ContextualComposition.NativeLinearAugmentation

@[expose] public section
/-! The genuinely native single-parent continuation step. Arbitrary
carrier-changing continuation arrows preserve the attached augmentation
when they preserve the original continuation augmentation. The outer
parent reduction is an independent, still opaque map. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open Functor.LaxMonoidal
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

theorem postPointwise_aug_preserves {I J : C} {A B : Aug ℙ I} (p : AugHom ℙ A B) (q : I ⟶ J) :
    p.native.comp (changeAugUnit B q).ε = (changeAugUnit A q).ε := by
  let r : Hom ℙ (terminalShape I) (terminalShape J) := pointwiseNative (fun _ : Fin 1 => q)
  change p.native.comp (B.ε.comp r) = A.ε.comp r
  rw [← Hom.comp_assoc, p.preserves]

noncomputable def changeAugUnit_map {I J : C} {A B : Aug ℙ I} (p : AugHom ℙ A B) (q : I ⟶ J) :
    AugHom ℙ (changeAugUnit A q) (changeAugUnit B q) :=
  ⟨p.native, postPointwise_aug_preserves p q⟩

set_option backward.isDefEq.respectTransparency false in
theorem totalAug_changeUnit {I J : C} (A : Family C) (p : totalFold A ⟶ I) (q : I ⟶ J) :
    changeAugUnit (totalAug A p) q = totalAug A (p ≫ q) := by
  apply congrArg (Aug.mk A)
  change (totalAug A p).ε.comp (pointwiseNative (fun _ : Fin 1 => q)) = _
  rw [native_post_pointwise]
  apply congrArg (Hom.mk (S:=ℙ) (A:=A) (B:=terminalShape J) (terminalCarrier A.n))
  funext j
  change (eqToHom (congrArg (fold 𝒮 Z A.val) (fibreList_terminal A.n j)) ≫ p) ≫ q =
    eqToHom (congrArg (fold 𝒮 Z A.val) (fibreList_terminal A.n j)) ≫ p ≫ q
  rw [Category.assoc]

variable (T : Bi (coeff (C:=C))) (a : C)

abbrev leftFactor : C ⥤ C where
  obj x := T.obj a x
  map f := T.map (𝟙 a) f
  map_id x := T.map_id a x
  map_comp f g := by
    simpa only [coeff, Category.id_comp] using (T.map_seq (𝟙 a) (𝟙 a) f g)

variable [(leftFactor T a).LaxBraided]

noncomputable def attachParent {I J : C} (A : Aug ℙ I)
    (q : T.obj a I ⟶ J) : Aug ℙ J :=
  changeAugUnit (linearAug (leftFactor T a) A) q

/-- The actual native continuation map keeps its carrier and whole-fibre
gather through the fixed parent coefficient. -/
noncomputable def attachParentMap {I J : C} {A B : Aug ℙ I}
    (p : AugHom ℙ A B) (q : T.obj a I ⟶ J) :
    AugHom ℙ (attachParent T a A q) (attachParent T a B q) :=
  changeAugUnit_map (linearAugMap (leftFactor T a) p) q

set_option backward.isDefEq.respectTransparency false in
theorem attachParent_total {I J : C} (A : Family C) (p : totalFold A ⟶ I) (q : T.obj a I ⟶ J) :
    attachParent T a (totalAug A p) q =
      totalAug (linearFamily (leftFactor T a) A)
        (Lin.collect (linearFunctor (leftFactor T a)) A.val (List.finRange A.n) ≫
          T.map (𝟙 a) p ≫ q) := by
  unfold attachParent
  rw [linearTotalAug, totalAug_changeUnit, Category.assoc]

variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

/-- The chosen lax braided structure must be the actual nullary and
binary gather already used by the dependent operation (not a different
gather chosen for this proof). -/
def SameLeftGather : Prop :=
  ε (leftFactor T a) = L.nil a ∧ ∀ x y, μ (leftFactor T a) x y = L.cons a x y

set_option backward.isDefEq.respectTransparency false in
theorem leftFactor_sameCollect (h : SameLeftGather T a L) {X : Type*} (A : X → C) (xs : List X) :
    Lin.collect (linearFunctor (leftFactor T a)) A xs = Lin.collect (Lin.left L a) A xs := by
  induction xs with
  | nil => exact h.1
  | cons x xs ih =>
    change (𝟙 (T.obj a (A x)) ⊗ₘ Lin.collect (linearFunctor (leftFactor T a)) A xs) ≫
        μ (leftFactor T a) (A x) (fold 𝒮 Z A xs) =
      (𝟙 (T.obj a (A x)) ⊗ₘ Lin.collect (Lin.left L a) A xs) ≫
        L.cons a (A x) (fold 𝒮 Z A xs)
    rw [ih, h.2]

set_option backward.isDefEq.respectTransparency false in
theorem attachParent_exact_cell {I J : C} {A B : Aug ℙ I} (p : AugHom ℙ A B)
    (q : T.obj a I ⟶ J) (h : SameLeftGather T a L) (j : Fin B.base.n) :
    (attachParentMap T a p q).native.cell j =
      Lin.collect (Lin.left L a) A.base.val (fibreList p.native.addr j) ≫
        T.map (𝟙 a) (p.native.cell j) := by
  have e := leftFactor_sameCollect T a L h A.base.val (fibreList p.native.addr j)
  change Lin.collect (linearFunctor (leftFactor T a)) A.base.val (fibreList p.native.addr j) ≫
      T.map (𝟙 a) (p.native.cell j) = _
  exact congrArg (fun t => t ≫ T.map (𝟙 a) (p.native.cell j)) e

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
