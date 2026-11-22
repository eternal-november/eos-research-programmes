module
public import ContextualComposition.NativeTerminalChart

@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

noncomputable def pointwiseNative {n : Nat} {A B : Fin n → C} (p : ∀ i, A i ⟶ B i) :
    Hom ℙ ⟨n,A⟩ ⟨n,B⟩ :=
  ⟨id, fun i => standardPushSingle A i ≫ p i⟩

set_option backward.isDefEq.respectTransparency false in
theorem native_post_pointwise {A : Family C} {n : Nat} {B D : Fin n → C}
    (p : Hom ℙ A ⟨n,B⟩) (q : ∀ i, B i ⟶ D i) :
    p.comp (pointwiseNative q) = Hom.mk (S:=ℙ) (A:=A) (B:=⟨n,D⟩) p.addr (fun i => p.cell i ≫ q i) := by
  apply congrArg (Hom.mk (S:=ℙ) (A:=A) (B:=⟨n,D⟩) p.addr)
  funext i
  change standardPushSplit p.addr id A.val i ≫
      (standardPushMap id p.cell i ≫ standardPushSingle B i ≫ q i) = _
  rw [reassoc_of% (standardPushSingle_natural p.cell i), ← Category.assoc]
  have h := standardPushSplit_right_unit p.addr A.val i
  change (standardPushSplit p.addr id A.val i ≫ standardPushSingle (standardPushObj p.addr A.val) i) ≫
      p.cell i ≫ q i = _
  rw [h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem native_pre_pointwise {n : Nat} {A B : Fin n → C} {D : Family C}
    (p : ∀ i, A i ⟶ B i) (q : Hom ℙ ⟨n,B⟩ D) :
    (pointwiseNative p).comp q =
      Hom.mk (S:=ℙ) (A:=⟨n,A⟩) (B:=D) q.addr (fun j => standardPushMap q.addr p j ≫ q.cell j) := by
  apply congrArg (Hom.mk (S:=ℙ) (A:=⟨n,A⟩) (B:=D) q.addr)
  funext j
  change standardPushSplit id q.addr A j ≫
      (standardPushMap q.addr (fun i => standardPushSingle A i ≫ p i) j ≫ q.cell j) = _
  rw [standardPushMap_comp, Category.assoc _ _ _, ← Category.assoc,
    standardPushSplit_left_unit, Category.id_comp]

variable (F : C ⥤ C) [F.LaxBraided]
set_option backward.isDefEq.respectTransparency false in
theorem linearTotalAug {I : C} (A : Family C) (p : totalFold A ⟶ I) :
    linearAug F (totalAug A p) =
      totalAug (linearFamily F A) (Lin.collect (linearFunctor F) A.val (List.finRange A.n) ≫ F.map p) := by
  have h : (linearAug F (totalAug A p)).ε =
      (totalAug (linearFamily F A)
        (Lin.collect (linearFunctor F) A.val (List.finRange A.n) ≫ F.map p)).ε := by
    apply congrArg (Hom.mk (S:=ℙ) (A:=linearFamily F A) (B:=terminalShape (F.obj I)) (terminalCarrier A.n))
    funext j
    let e := fibreList_terminal A.n j
    change Lin.collect (linearFunctor F) A.val (fibreList (terminalCarrier A.n) j) ≫
      F.map (eqToHom (congrArg (fold 𝒮 Z A.val) e) ≫ p) =
      eqToHom (congrArg (fold 𝒮 Z (fun i => F.obj (A.val i))) e) ≫
        Lin.collect (linearFunctor F) A.val (List.finRange A.n) ≫ F.map p
    rw [F.map_comp, ← Category.assoc, collect_list_congr F A.val e, Category.assoc]
  exact congrArg (Aug.mk (linearFamily F A)) h

variable {F} {G : C ⥤ C} [G.LaxBraided] (η : F ⟶ G)
set_option backward.isDefEq.respectTransparency false in
/-- A factor natural transformation respecting the declared binary and
nullary gathers gives an actual native square on arbitrary carrier maps. -/
theorem linearNative_natural {A B : Family C} (p : Hom ℙ A B)
    (H : LinSquare (linearFunctor F) (linearFunctor G) η.app) :
    (linearNativeMap F p).comp (pointwiseNative (fun j => η.app (B.val j))) =
      (pointwiseNative (fun i => η.app (A.val i))).comp (linearNativeMap G p) := by
  rw [native_post_pointwise, native_pre_pointwise]
  apply congrArg (Hom.mk (S:=ℙ) (A:=linearFamily F A) (B:=linearFamily G B) p.addr)
  funext j
  let r := p.cell j
  let xs := fibreList p.addr j
  let a := standardPushObj p.addr A.val j
  let b := B.val j
  let k := Lin.collect (linearFunctor F) A.val xs
  let l := Lin.collect (linearFunctor G) A.val xs
  let u := act 𝒮 Z (fun i => η.app (A.val i)) xs
  change (k ≫ F.map r) ≫ η.app b = u ≫ l ≫ G.map r
  have h : k ≫ η.app a = u ≫ l := H.collect A.val xs
  have n : F.map r ≫ η.app b = η.app a ≫ G.map r := η.naturality r
  rw [Category.assoc, n, ← Category.assoc, h, Category.assoc]


/-- Postcompose the one actual augmentation. No map between augmented
families is made out of a family of elementwise augmentation maps. -/
noncomputable def changeAugUnit {I J : C} (A : Aug ℙ I) (q : I ⟶ J) : Aug ℙ J where
  base := A.base
  ε := A.ε.comp (pointwiseNative (fun _ : Fin 1 => q))

noncomputable def linearAugComparison {I : C} (A : Aug ℙ I)
    (H : LinSquare (linearFunctor F) (linearFunctor G) η.app) :
    AugHom ℙ (changeAugUnit (linearAug F A) (η.app I)) (linearAug G A) where
  native := pointwiseNative (fun i => η.app (A.base.val i))
  preserves := (linearNative_natural η A.ε H).symm

theorem linearAugComparison_natural {I : C} {A B : Aug ℙ I}
    (p : AugHom ℙ A B) (H : LinSquare (linearFunctor F) (linearFunctor G) η.app) :
    (linearNativeMap F p.native).comp (linearAugComparison η B H).native =
      (linearAugComparison η A H).native.comp (linearNativeMap G p.native) :=
  linearNative_natural η p.native H

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
