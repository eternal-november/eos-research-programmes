module
public import ContextualComposition.NativeParentChange
public import ContextualComposition.NativeFibreRestriction

@[expose] public section
/-! The rectangle uses the same right and left unary gathers as the
native linear action, not independently selected aggregators. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open Functor.LaxMonoidal
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C
variable {T : Bi (coeff (C:=C))}

/-- Multiplication in the first slot. -/
abbrev rightFactor (a : C) : C ⥤ C where
  obj x := T.obj x a
  map f := T.map f (𝟙 a)
  map_id x := T.map_id x a
  map_comp f g := by
    simpa only [coeff, Category.id_comp] using (T.map_seq f g (𝟙 a) (𝟙 a))

variable (R : Gather 𝒮 T Z) (L : LeftGather 𝒮 T Z)
variable {a : C} [(rightFactor (T:=T) a).LaxBraided]

def SameRightGather (R : Gather 𝒮 T Z) (a : C) [(rightFactor (T:=T) a).LaxBraided] : Prop :=
  ε (rightFactor (T:=T) a) = R.nil a ∧
    ∀ x y, μ (rightFactor (T:=T) a) x y = R.cons x y a

set_option backward.isDefEq.respectTransparency false in
theorem rightFactor_sameCollect (R : Gather 𝒮 T Z) (_h : SameRightGather R a) {X : Type*}
    (A : X → C) (xs : List X) :
    Lin.collect (linearFunctor (rightFactor (T:=T) a)) A xs = DependentFibre.gather R A a xs := by
  induction xs with
  | nil => exact _h.1
  | cons x xs ih =>
    change (𝟙 (T.obj (A x) a) ⊗ₘ Lin.collect (linearFunctor (rightFactor (T:=T) a)) A xs) ≫
      μ (rightFactor (T:=T) a) (A x) (fold 𝒮 Z A xs) =
      (𝟙 (T.obj (A x) a) ⊗ₘ DependentFibre.gather R A a xs) ≫ R.cons (A x) (fold 𝒮 Z A xs) a
    rw [ih, _h.2]

theorem innerLeft_collect (L : LeftGather 𝒮 T Z) {X : Type*} (a : C) (V : X → C) (xs : List X) :
    innerLeft L a V xs = Lin.collect (Lin.left L a) V xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [innerLeft, Lin.collect, ih]

set_option backward.isDefEq.respectTransparency false in
/-- The scheduled rectangle, with exact categorical gathers filled by
native unary functors at the relevant fixed coefficients. -/
theorem rect_native_gathers (R : Gather 𝒮 T Z) (L : LeftGather 𝒮 T Z) {X Y : Type w} (V : X → C) (W : Y → C)
    (xs : List X) (ys : List Y)
    [_right : (rightFactor (T:=T) (fold 𝒮 Z W ys)).LaxBraided]
    [_left : ∀ x : X, (leftFactor T (V x)).LaxBraided]
    (hr : SameRightGather R (fold 𝒮 Z W ys))
    (hl : ∀ x, SameLeftGather T (V x) L) :
    DependentFibre.rect (K:=coeff (C:=C)) R L V W xs ys =
      act 𝒮 Z (fun x => Lin.collect (linearFunctor (leftFactor T (V x))) W ys) xs ≫
      Lin.collect (linearFunctor (rightFactor (T:=T) (fold 𝒮 Z W ys))) V xs := by
  change act 𝒮 Z (fun x => innerLeft L (V x) W ys) xs ≫
      DependentFibre.gather R V (fold 𝒮 Z W ys) xs = _
  rw [rightFactor_sameCollect R hr]
  congr 1
  apply congrArg (fun m => act 𝒮 Z m xs)
  funext x
  rw [innerLeft_collect, leftFactor_sameCollect T (V x) L (hl x)]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
