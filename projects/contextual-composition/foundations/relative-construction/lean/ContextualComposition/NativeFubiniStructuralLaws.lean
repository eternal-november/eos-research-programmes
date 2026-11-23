module
public import ContextualComposition.NativeDependentTriangle
@[expose] public section

/-! The local mixed Fubini coefficient diagrams. The regrouping law is
the monoidality of the tensor functor; the dependent-associativity law
is the monoidality of its associator. The two six-input paths differ. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [cat : Category.{v} C]

def MedialRegroup {T : Bi (coeff (C:=C))} {I : C} (P : TensorPrimitive T) (M : Middle T I) : Prop :=
  ∀ a b c d e f : C,
    T.map (M.cell a b c d) (𝟙 (T.obj e f)) ≫
      M.cell (T.obj a c) (T.obj b d) e f ≫ T.map (P.assoc a c e) (P.assoc b d f) =
    P.assoc (T.obj a b) (T.obj c d) (T.obj e f) ≫
      T.map (𝟙 (T.obj a b)) (M.cell c d e f) ≫ M.cell a b (T.obj c e) (T.obj d f)

def MedialDependentAssoc {T : Bi (coeff (C:=C))} {I : C}
    (P : TensorPrimitive T) (M : Middle T I) : Prop :=
  ∀ a b c d e f : C,
    M.cell (T.obj a b) c (T.obj d e) f ≫
      T.map (M.cell a b d e) (𝟙 (T.obj c f)) ≫ P.assoc (T.obj a d) (T.obj b e) (T.obj c f) =
    T.map (P.assoc a b c) (P.assoc d e f) ≫
      M.cell a (T.obj b c) d (T.obj e f) ≫ T.map (𝟙 (T.obj a d)) (M.cell b c e f)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem standardMedialRegroup (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul) :
    MedialRegroup (@tensorPrimitives C cat mul br)
      (additiveMiddle (@Additive.ofBraided C cat mul br)) := by
  intro a b c d e f
  letI := mul
  letI := br
  change (tensorμ a b c d ⊗ₘ 𝟙 (e ⊗ f)) ≫
      tensorμ (a ⊗ c) (b ⊗ d) e f ≫ ((α_ a c e).hom ⊗ₘ (α_ b d f).hom) =
    (α_ (a ⊗ b) (c ⊗ d) (e ⊗ f)).hom ≫
      (𝟙 (a ⊗ b) ⊗ₘ tensorμ c d e f) ≫ tensorμ a b (c ⊗ e) (d ⊗ f)
  rw [tensorHom_id, id_tensorHom]
  exact tensor_associativity a b c d e f

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem standardMedialDependentAssoc (mul : MonoidalCategory C) (br : @BraidedCategory C cat mul) :
    MedialDependentAssoc (@tensorPrimitives C cat mul br)
      (additiveMiddle (@Additive.ofBraided C cat mul br)) := by
  intro a b c d e f
  letI := mul
  letI := br
  change tensorμ (a ⊗ b) c (d ⊗ e) f ≫
      (tensorμ a b d e ⊗ₘ 𝟙 (c ⊗ f)) ≫ (α_ (a ⊗ d) (b ⊗ e) (c ⊗ f)).hom =
    ((α_ a b c).hom ⊗ₘ (α_ d e f).hom) ≫
      tensorμ a (b ⊗ c) d (e ⊗ f) ≫ (𝟙 (a ⊗ d) ⊗ₘ tensorμ b c e f)
  rw [tensorHom_id, id_tensorHom]
  exact associator_monoidal a b c d e f

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
