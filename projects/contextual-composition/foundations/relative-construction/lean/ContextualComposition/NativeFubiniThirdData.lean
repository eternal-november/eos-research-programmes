module
public import ContextualComposition.NativeFubiniScalarOrder
@[expose] public section

/-! Three actual dependent levels and their two bracketings. The third
whole augmentations remain indexed by both preceding raw addresses. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {I : C}

structure OrderedDependentThirdData (A : OrderedDependentAugData I) where
  W : Type u
  eqW : DecidableEq W
  ws : A.X → A.U → List W
  D : A.X → A.U → W → C
  unique : ∀ x ∈ A.xs, ∀ y ∈ A.us x, (ws x y).Nodup
  γ : ∀ x y, fold 𝒮 Zₐ (D x y) (ws x y) ⟶ I

namespace OrderedDependentThirdData
variable {T : Bi (coeff (C:=C))} {A B : OrderedDependentAugData I}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (D : OrderedDependentThirdData A) (E : OrderedDependentThirdData B)

def tailData (x : A.X) (hx : x ∈ A.xs) : OrderedDependentAugData I where
  X := A.U
  U := D.W
  eqX := A.eqU
  eqU := D.eqW
  xs := A.us x
  us := D.ws x
  V := A.A x
  A := D.D x
  xs_unique := A.us_unique x hx
  us_unique := D.unique x hx
  ε := A.δ x
  δ := D.γ x

def leftData : OrderedDependentAugData I where
  X := A.X × A.U
  U := D.W
  eqX := @instDecidableEqProd A.X A.U A.eqX A.eqU
  eqU := D.eqW
  xs := dependentWord A.xs A.us
  us t := D.ws t.1 t.2
  V := dependentLabels (T:=T) A.V A.A
  A t := D.D t.1 t.2
  xs_unique := dependentWord_nodup A.xs_unique A.us_unique
  us_unique t ht :=
    let h := (dependentWord_mem A.xs A.us t).mp ht
    D.unique t.1 h.1 t.2 h.2
  ε := A.accCell R L J
  δ t := D.γ t.1 t.2

def rightData : OrderedDependentAugData I where
  X := A.X
  U := A.U × D.W
  eqX := A.eqX
  eqU := @instDecidableEqProd A.U D.W A.eqU D.eqW
  xs := A.xs
  us x := dependentWord (A.us x) (D.ws x)
  V := A.V
  A x := dependentLabels (T:=T) (A.A x) (D.D x)
  xs_unique := A.xs_unique
  us_unique x hx := dependentWord_nodup (A.us_unique x hx) (D.unique x hx)
  ε := A.ε
  δ x := dependentWordAugCell R L J (A.us x) (D.ws x) (A.A x) (D.D x) (indexedAugmentation (D.γ x)) (A.δ x)

def product : OrderedDependentThirdData (A.product R L J B) where
  W := D.W × E.W
  eqW := @instDecidableEqProd D.W E.W D.eqW E.eqW
  ws x y := (D.ws x.1 y.1).product (E.ws x.2 y.2)
  D x y := crossLabel T (D.D x.1 y.1) (E.D x.2 y.2)
  unique x hx y hy := by
    have h := (mem_ordered_product A.xs B.xs x).mp hx
    have k := (mem_ordered_product (A.us x.1) (B.us x.2) y).mp hy
    exact nodup_product_word (D.unique x.1 h.1 y.1 k.1) (E.unique x.2 h.2 y.2 k.2)
  γ x y := rectangularWordAugCell R L (J.ρ I) (D.D x.1 y.1) (E.D x.2 y.2)
    (D.ws x.1 y.1) (E.ws x.2 y.2) (D.γ x.1 y.1) (E.γ x.2 y.2)

variable (P : TensorPrimitive T) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))

set_option backward.isDefEq.respectTransparency false in
noncomputable def associator :
    NativeAugmentedIso ((D.leftData R L J).accumulate R L J) ((D.rightData R L J).accumulate R L J) :=
  dependentAssocIso R L J P NL Q U A.xs A.us D.ws A.V A.A D.D A.ε A.δ D.γ hl ι
    (dependentWord_nodup (D.rightData R L J).xs_unique (D.rightData R L J).us_unique)

end OrderedDependentThirdData

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
