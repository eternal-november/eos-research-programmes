module
public import ContextualComposition.RaggedGrid
public import ContextualComposition.StandardRigLinearity
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C]
variable (S : Additive (C:=C))
abbrev cross (h : ∀ a b c d, (S.middle a b c d).hom ≫ (S.middle a c b d).hom = 𝟙 _) :
    AddCross (binary S.sum) S.zero where
  merge := S.mergeZero.hom
  empty := S.mergeZero.inv
  middle a b c d := (S.middle a b c d).hom
  invol := h
  natural := S.middle_natural

variable {S}
theorem cross_binary (K : GridData S)
    (h : ∀ a b c d, (S.middle a b c d).hom ≫ (S.middle a c b d).hom = 𝟙 _) :
    GridBinary (cross S h) (gather K) (leftGather K) where
  mergeInv := S.mergeZero.inv_hom_id
  splitInv := S.mergeZero.hom_inv_id
  bin a b := by
    let D := K.leftSplit (S.sum.obj a b)
    let E := (K.leftSplit a).pointwise (K.leftSplit b)
    let t := K.rightDist a b
    have tb := K.rightDist_preserves a b
    have flip {x y z w : C} (p : x ≅ y) (q : z ≅ w) (f : x ≅ z) (g : y ≅ w)
        (e : f.hom ≫ q.hom = p.hom ≫ g.hom) :
        q.inv ≫ f.inv = g.inv ≫ p.inv := by
      apply (cancel_mono (f.hom ≫ q.hom)).mp
      rw [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      rw [e, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
    constructor
    · have e : (t.app S.zero).hom ≫ E.nil.hom = D.nil.hom ≫ (Iso.refl S.zero).hom := by
        rw [Iso.refl_hom, Category.comp_id]
        exact tb.nil
      have w := flip D.nil E.nil (t.app S.zero) (Iso.refl S.zero) e
      rw [Iso.refl_inv, Category.id_comp] at w
      exact w
    · intro c d
      let p := D.bin c d
      let q := E.bin c d
      let g := S.sum.mapIso (t.app c) (t.app d)
      have hm : (S.middle _ _ _ _).inv =
          (S.middle (K.mul.obj a c) (K.mul.obj b c) (K.mul.obj a d) (K.mul.obj b d)).hom := by
        apply (cancel_epi (S.middle (K.mul.obj a c) (K.mul.obj a d) (K.mul.obj b c) (K.mul.obj b d)).hom).mp
        rw [Iso.hom_inv_id, h]
      change (_ ≫ _) ≫ (t.app (S.sum.obj c d)).inv = g.inv ≫ p.inv
      have e := tb.bin c d
      have ee := flip p q (t.app (S.sum.obj c d)) g e
      change ((S.middle (K.mul.obj a c) (K.mul.obj a d) (K.mul.obj b c) (K.mul.obj b d)).inv ≫
        S.sum.map ((K.leftSplit a).bin c d).inv ((K.leftSplit b).bin c d).inv) ≫ _ = _ at ee
      rw [hm] at ee
      exact ee
  nil := by
    let D := K.leftSplit S.zero
    let E := S.zeroSplit
    let t := K.absorbLeft
    have nt := K.absorbLeft_preserves
    constructor
    · change 𝟙 _ ≫ (t.app S.zero).inv = D.nil.inv
      rw [Category.id_comp]
      apply (cancel_mono (t.app S.zero).hom).mp
      rw [(t.app S.zero).inv_hom_id]
      have eq : (t.app S.zero).hom = D.nil.hom := by
        have e := nt.nil
        change (t.app S.zero).hom ≫ 𝟙 _ = D.nil.hom at e
        exact (Category.comp_id _).symm.trans e
      rw [eq, D.nil.inv_hom_id]
      rfl
    · intro a b
      let q := E.bin a b
      let p := D.bin a b
      change q.inv ≫ (t.app (S.sum.obj a b)).inv =
        S.sum.map (t.app a).inv (t.app b).inv ≫ p.inv
      let g := S.sum.mapIso (t.app a) (t.app b)
      change q.inv ≫ (t.app (S.sum.obj a b)).inv = g.inv ≫ p.inv
      apply (cancel_mono ((t.app (S.sum.obj a b)).hom ≫ q.hom)).mp
      rw [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
      have e : (t.app (S.sum.obj a b)).hom ≫ q.hom = p.hom ≫ g.hom := nt.bin a b
      rw [e, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

theorem add_middle_involutive [MonoidalCategory C] [SymmetricCategory C] (a b c d : C) :
    ((Additive.ofBraided (C:=C)).middle a b c d).hom ≫
      ((Additive.ofBraided (C:=C)).middle a c b d).hom = 𝟙 _ := by
  change tensorμ a b c d ≫ tensorμ a c b d = 𝟙 _
  have h : tensorμ a c b d = tensorδ a b c d := by
    simp only [tensorμ, tensorδ, SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [h, tensorμ_tensorδ]
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
