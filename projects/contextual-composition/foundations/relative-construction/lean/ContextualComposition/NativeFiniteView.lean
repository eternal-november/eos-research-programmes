module
public import ContextualComposition.NativeFubiniTreePathCoherence
@[expose] public section

/-! A native finite family can be named in an ambient address type.
The finite word is its original position enumeration, not a quotient
by coefficient labels or a requirement that the ambient type is finite. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

structure NativeFiniteView (P : Family C) (X : Type w) where
  tag : Fin P.n → X
  tag_injective : Function.Injective tag
  label : X → C
  label_tag : ∀ i, label (tag i) = P.val i

namespace NativeFiniteView
variable {X : Type w} {P : Family C} (p : NativeFiniteView P X)

def word : List X := (List.finRange P.n).map p.tag

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem word_nodup : p.word.Nodup :=
  (List.nodup_finRange P.n).map p.tag (fun _ _ hf e => hf (p.tag_injective e))

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem word_len : p.word.length = P.n := by simp [word]

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem word_get (i : Fin p.word.length) :
    p.word[i] = p.tag (Fin.cast p.word_len i) := by
  have hi : i.val < (List.finRange P.n).length := (List.length_finRange (n:=P.n)).symm ▸ (Fin.cast p.word_len i).isLt
  change ((List.finRange P.n).map p.tag)[i.val] = _
  have h : ((List.finRange P.n).map p.tag)[i.val] = p.tag ((List.finRange P.n)[i.val]'hi) :=
    List.getElem_map p.tag
  exact h.trans (congrArg p.tag (Fin.ext (by rw [List.getElem_finRange]; rfl)))

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem family_eq : wordFamily p.label p.word = P := by
  have L : (wordFamily p.label p.word).n = P.n := p.word_len
  have E : ∀ i, (wordFamily p.label p.word).val i = P.val (Fin.cast L i) :=
    fun i => (congrArg p.label (p.word_get i)).trans (p.label_tag _)
  have shape {A B : Family C} (h : A.n = B.n) (v : ∀ i, A.val i = B.val (Fin.cast h i)) : A = B := by
    cases A with | mk n a =>
      cases B with | mk m b =>
        change n = m at h
        subst m
        exact congrArg (Family.mk n) (funext v)
  exact shape L E

noncomputable def augCell {I : C} (A : Aug ℙ I) (p : NativeFiniteView A.base X) :
    fold 𝒮 Zₐ p.label p.word ⟶ I :=
  eqToHom ((wordTotalPin p.label p.word).symm.trans (congrArg totalFold p.family_eq)) ≫ totalNativeCell A

set_option backward.isDefEq.respectTransparency false in
theorem aug_eq {I : C} (A : Aug ℙ I) (p : NativeFiniteView A.base X) :
    wordAug p.label p.word (p.augCell A) = A := by
  rw [wordAug_total]
  unfold augCell
  rw [← Category.assoc, eqToHom_trans]
  have h {P Q : Family C} (e : P = Q) (a : totalFold Q ⟶ I) :
      totalAug P (eqToHom (congrArg totalFold e) ≫ a) = totalAug Q a := by
    subst Q
    rw [eqToHom_refl, Category.id_comp]
  change totalAug (wordFamily p.label p.word)
    (eqToHom (congrArg totalFold p.family_eq) ≫ totalNativeCell A) = A
  rw [h p.family_eq, totalAug_nativeCell]

end NativeFiniteView

/-- The original finite positions, with no retagging at all. -/
def originalFiniteView (P : Family C) : NativeFiniteView P (Fin P.n) where
  tag := id
  tag_injective := Function.injective_id
  label := P.val
  label_tag _ := rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
