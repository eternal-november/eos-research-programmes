module
public import ContextualComposition.NativeIndependentSwapNaturality
@[expose] public section

/-! Symmetry is involutive on the actual native augmented product. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (ι : ∀ a b, IsIso (P.swap a b))
variable {X Y : Type u} (A : X → C) (B : Y → C)
variable (xs : List X) (ys : List Y)
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (hx : xs.Nodup) (hy : ys.Nodup)

set_option backward.isDefEq.respectTransparency false in
theorem independentSwap_involutive
    (law : ∀ a b, P.swap a b ≫ P.swap b a = 𝟙 (T.obj a b)) :
    (independentSwapIso R L J P Q N swap_unit ι A B xs ys p q hx hy).hom.comp
      (independentSwapIso R L J P Q N swap_unit ι B A ys xs q p hy hx).hom =
    AugHom.ident (independentAug R L (J.ρ I) (wordAug A xs p) (wordAug B ys q)) := by
  let F := (rawWordFrame A xs hx).tensor T (rawWordFrame B ys hy)
  let G := (rawWordFrame B ys hy).tensor T (rawWordFrame A xs hx)
  let e := Equiv.prodComm Y X
  let v (z : X × Y) := T.obj (A z.1) (B z.2)
  let w (z : X × Y) := T.obj (B z.2) (A z.1)
  let GG := G.relabel e e.injective w (fun _ => rfl)
  let u (z : X × Y) : v z ⟶ w z := P.swap (A z.1) (B z.2)
  let k (z : X × Y) : w z ⟶ v z := P.swap (B z.2) (A z.1)
  let a := (independentSwapIso R L J P Q N swap_unit ι A B xs ys p q hx hy).hom
  let b := (independentSwapIso R L J P Q N swap_unit ι B A ys xs q p hy hx).hom
  have e₀ : RawSingletonTrace F GG u a.native :=
    independentSwapIso_trace R L J P Q N swap_unit ι A B xs ys p q hx hy
  have e₁ : RawSingletonTrace GG F k b.native := by
    have h := (independentSwapIso_trace R L J P Q N swap_unit ι B A ys xs q p hy hx).relabel e e.injective
      w v (fun _ => rfl) (fun _ => rfl) k (fun _ => HEq.rfl)
    exact h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  apply AugHom.ext
  exact (e₀.comp e₁).eq (RawSingletonTrace.ident F) (fun i =>
    law (A (F.read i).1) (B (F.read i).2))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem standardIndependentSwap_involutive (mul : MonoidalCategory C) (symm : @SymmetricCategory C cat mul) :
    ∀ a b : C,
    (@tensorPrimitives C cat mul symm.toBraidedCategory).swap a b ≫
      (@tensorPrimitives C cat mul symm.toBraidedCategory).swap b a =
        𝟙 ((binary (@Binary.ofMonoidal C cat mul)).obj a b) := by
  letI := mul
  letI := symm
  exact SymmetricCategory.symmetry

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
