module
public import ContextualComposition.NativeDependentStructuralWhisker
@[expose] public section

/-! The native pentagon on one ordered raw chart. No augmentation
compatibility is assumed for composites: all five input edges are
individually augmented and only the local coefficient pentagon is used. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem wordPointwise_pentagon {X : Type u} {I : C} (xs : List X)
    {A B D E F : X → C} {a : fold 𝒮 Zₐ A xs ⟶ I} {b : fold 𝒮 Zₐ B xs ⟶ I}
    {d : fold 𝒮 Zₐ D xs ⟶ I} {e : fold 𝒮 Zₐ E xs ⟶ I} {f : fold 𝒮 Zₐ F xs ⟶ I}
    (p : AugHom ℙ (wordAug A xs a) (wordAug B xs b))
    (q : AugHom ℙ (wordAug B xs b) (wordAug D xs d))
    (r : AugHom ℙ (wordAug D xs d) (wordAug E xs e))
    (s : AugHom ℙ (wordAug A xs a) (wordAug F xs f))
    (t : AugHom ℙ (wordAug F xs f) (wordAug E xs e))
    {p₀ : ∀ x, A x ⟶ B x} {q₀ : ∀ x, B x ⟶ D x} {r₀ : ∀ x, D x ⟶ E x}
    {s₀ : ∀ x, A x ⟶ F x} {t₀ : ∀ x, F x ⟶ E x}
    (hp : p.native = wordPointwise xs p₀) (hq : q.native = wordPointwise xs q₀)
    (hr : r.native = wordPointwise xs r₀) (hs : s.native = wordPointwise xs s₀)
    (ht : t.native = wordPointwise xs t₀)
    (h : ∀ x ∈ xs, (p₀ x ≫ q₀ x) ≫ r₀ x = s₀ x ≫ t₀ x) :
    (p.comp q).comp r = s.comp t := by
  apply AugHom.ext
  change (p.native.comp q.native).comp r.native = s.native.comp t.native
  rw [hp,hq,hr,hs,ht,wordPointwise_comp,wordPointwise_comp,wordPointwise_comp]
  exact wordPointwise_eq_of_mem xs _ _ h

/-- The compositional law on multiplicative coefficients is local to four
objects. Its specialization to an independent standard multiplication
does not rely on either the additive symmetry or the rig distributors. -/
def MulPentagon {T : Bi (coeff (C:=C))} (P : TensorPrimitive T) : Prop :=
  ∀ a b c d : C,
    (T.map (P.assoc a b c) (𝟙 d) ≫ P.assoc a (T.obj b c) d) ≫
        T.map (𝟙 a) (P.assoc b c d) =
      P.assoc (T.obj a b) c d ≫ P.assoc a b (T.obj c d)

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
set_option linter.style.haveILetI false in
theorem standardMulPentagon (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul) :
    MulPentagon (@tensorPrimitives C cat mul br) := by
  intro a b c d
  letI := mul
  change (((α_ a b c).hom ⊗ₘ 𝟙 d) ≫ (α_ a (b ⊗ c) d).hom) ≫
    (𝟙 a ⊗ₘ (α_ b c d).hom) =
    (α_ (a ⊗ b) c d).hom ≫ (α_ a b (c ⊗ d)).hom
  rw [tensorHom_id, id_tensorHom, Category.assoc]
  exact pentagon a b c d


set_option backward.isDefEq.respectTransparency false in
theorem AugHom.pentagon_of_pointwise_native_heq {X : Type u} {I : C} (xs : List X)
    {A B D E F : X → C} {a b d e f : Aug ℙ I}
    (ha : a.base = wordFamily A xs) (hb : b.base = wordFamily B xs)
    (hd : d.base = wordFamily D xs) (he : e.base = wordFamily E xs) (hf : f.base = wordFamily F xs)
    (p : AugHom ℙ a b) (q : AugHom ℙ b d) (r : AugHom ℙ d e)
    (s : AugHom ℙ a f) (t : AugHom ℙ f e)
    {p₀ : ∀ x, A x ⟶ B x} {q₀ : ∀ x, B x ⟶ D x} {r₀ : ∀ x, D x ⟶ E x}
    {s₀ : ∀ x, A x ⟶ F x} {t₀ : ∀ x, F x ⟶ E x}
    (hp : HEq p.native (wordPointwise xs p₀)) (hq : HEq q.native (wordPointwise xs q₀))
    (hr : HEq r.native (wordPointwise xs r₀)) (hs : HEq s.native (wordPointwise xs s₀))
    (ht : HEq t.native (wordPointwise xs t₀))
    (h : ∀ x ∈ xs, (p₀ x ≫ q₀ x) ≫ r₀ x = s₀ x ≫ t₀ x) :
    (p.comp q).comp r = s.comp t := by
  apply AugHom.ext
  have h₁ := nativeHom_comp_heq p.native q.native _ _ ha hb hd hp hq
  have h₂ := nativeHom_comp_heq (p.native.comp q.native) r.native _ _ ha hd he h₁ hr
  have h₃ := nativeHom_comp_heq s.native t.native _ _ ha hf he hs ht
  have k : ((wordPointwise xs p₀).comp (wordPointwise xs q₀)).comp (wordPointwise xs r₀) =
      (wordPointwise xs s₀).comp (wordPointwise xs t₀) := by
    rw [wordPointwise_comp, wordPointwise_comp, wordPointwise_comp]
    exact wordPointwise_eq_of_mem xs _ _ h
  exact eq_of_heq (h₂.trans ((heq_of_eq k).trans h₃.symm))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
