module
public import ContextualComposition.NativeFiniteView
@[expose] public section

/-! Present a native map in arbitrary injective names for its finite
positions. The actual fibre cell, including an empty one, is retained. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

namespace NativeFiniteView
variable {A B : Family C} {X : Type w} {Y : Type z} [DecidableEq Y]
variable (a : NativeFiniteView A X) (b : NativeFiniteView B Y)
variable (p : Hom (standardPush (C:=C)) A B) (f : X → Y)
variable (s : ∀ i, f (a.tag i) = b.tag (p.addr i))

omit [DecidableEq Y] in
include s in
theorem support : ∀ x ∈ a.word, f x ∈ b.word := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  rw [s i]
  exact List.mem_map.mpr ⟨p.addr i,List.mem_finRange _,rfl⟩

def castHom {A A' B B' : Family C} (p : Hom ℙ A B) (e : A' = A) (d : B' = B) : Hom ℙ A' B' :=
  e.symm ▸ d.symm ▸ p

theorem castHom_heq {A A' B B' : Family C} (p : Hom ℙ A B) (e : A' = A) (d : B' = B) :
    HEq (castHom p e d) p := by subst A'; subst B'; rfl

theorem castHom_addr {A A' B B' : Family C} (p : Hom ℙ A B) (e : A' = A) (d : B' = B)
    (i : Fin A'.n) :
    Fin.cast (congrArg Family.n d) ((castHom p e d).addr i) = p.addr (Fin.cast (congrArg Family.n e) i) := by
  subst A'; subst B'; rfl

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] in
include s in
theorem carrier :
    wordCarrier f (support a b p f s) b.word_nodup = (castHom p a.family_eq b.family_eq).addr := by
  funext i
  apply Fin.ext
  let x := wordCarrier f (support a b p f s) b.word_nodup i
  let y := (castHom p a.family_eq b.family_eq).addr i
  have hx := wordCarrier_get f (support a b p f s) b.word_nodup i
  have hy := castHom_addr p a.family_eq b.family_eq i
  have h : b.tag (Fin.cast b.word_len x) = b.tag (Fin.cast b.word_len y) :=
    (b.word_get x).symm.trans (hx.trans ((congrArg f (a.word_get i)).trans ((s _).trans (congrArg b.tag hy.symm))))
  exact congrArg (fun j : Fin B.n => j.val) (b.tag_injective h)

set_option backward.isDefEq.respectTransparency false in
noncomputable def cells
    (j : Fin b.word.length) : fold 𝒮 Zₐ a.label (wordFibre a.word f b.word[j]) ⟶ b.label b.word[j] :=
  let d := castHom p a.family_eq b.family_eq
  let e := carrier a b p f s
  let a₀ := wordCarrier_fibre_pin f (support a b p f s) b.word_nodup a.label j
  let a₁ := congrArg (fun f => standardPushObj f (wordFamily a.label a.word).val j) e
  eqToHom (a₀.symm.trans a₁) ≫ d.cell j

set_option backward.isDefEq.respectTransparency false in
theorem native_eq :
    wordNativeMap f (support a b p f s) b.word_nodup a.label b.label (cells a b p f s) =
      castHom p a.family_eq b.family_eq := by
  let d := castHom p a.family_eq b.family_eq
  let e := carrier a b p f s
  apply native_hom_iff_cell e _ _ |>.2
  intro j
  let pin := wordCarrier_fibre_pin f (support a b p f s) b.word_nodup a.label j
  let k := congrArg (fun f => standardPushObj f (wordFamily a.label a.word).val j) e
  change eqToHom pin ≫ eqToHom (pin.symm.trans k) ≫ d.cell j = eqToHom k ≫ d.cell j
  rw [eqToHom_trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The same actual cells, indexed by the supported raw target address
rather than its numerical word position. -/
noncomputable def cellAt (y : Y) (h : y ∈ b.word) :
    fold 𝒮 Zₐ a.label (wordFibre a.word f y) ⟶ b.label y :=
  let r := wordPositions b.word b.word_nodup
  let j := r.symm ⟨y,h⟩
  let e : b.word[j] = y := congrArg Subtype.val (r.apply_symm_apply ⟨y,h⟩)
  eqToHom (congrArg (fun z => fold 𝒮 Zₐ a.label (wordFibre a.word f z)) e.symm) ≫
    cells a b p f s j ≫ eqToHom (congrArg b.label e)

set_option backward.isDefEq.respectTransparency false in
theorem cellAt_get (j : Fin b.word.length) :
    cellAt a b p f s b.word[j] (List.getElem_mem _) = cells a b p f s j := by

  let r := wordPositions b.word b.word_nodup
  let i := r.symm ⟨b.word[j],List.getElem_mem _⟩
  have h : i = j := r.symm_apply_apply j
  have aux (i j : Fin b.word.length) (h : i = j) (e : b.word[i] = b.word[j]) :
      eqToHom (congrArg (fun z => fold 𝒮 Zₐ a.label (wordFibre a.word f z)) e.symm) ≫
        cells a b p f s i ≫ eqToHom (congrArg b.label e) = cells a b p f s j := by
    subst j
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact aux i j h (congrArg Subtype.val (r.apply_symm_apply ⟨b.word[j],List.getElem_mem _⟩))

set_option backward.isDefEq.respectTransparency false in
theorem wordMap_cells_heq :
    HEq (wordNativeMap f (support a b p f s) b.word_nodup a.label b.label
      (fun j => cellAt a b p f s b.word[j] (List.getElem_mem _))) p := by
  have e : (fun j : Fin b.word.length => cellAt a b p f s b.word[j] (List.getElem_mem _)) = cells a b p f s :=
    funext (cellAt_get a b p f s)
  rw [e, native_eq]
  exact castHom_heq p a.family_eq b.family_eq

set_option backward.isDefEq.respectTransparency false in
theorem preserving_of_heq {I : C} {A B A' B' : Aug ℙ I} (e : A = A') (d : B = B')
    (p : AugHom ℙ A' B') (f : Hom ℙ A.base B.base) (h : HEq f p.native) :
    f.comp B.ε = A.ε := by
  subst A'; subst B'
  exact (eq_of_heq h).symm ▸ p.preserves

set_option backward.isDefEq.respectTransparency false in
theorem wordMap_preserves {I : C} {A B : Aug ℙ I}
    (a : NativeFiniteView A.base X) (b : NativeFiniteView B.base Y)
    (p : AugHom ℙ A B) (f : X → Y) (s : ∀ i, f (a.tag i) = b.tag (p.native.addr i)) :
    (wordNativeMap f (support a b p.native f s) b.word_nodup a.label b.label
      (fun j => cellAt a b p.native f s b.word[j] (List.getElem_mem _))).comp
      (wordAug b.label b.word (b.augCell B)).ε =
    (wordAug a.label a.word (a.augCell A)).ε :=
  preserving_of_heq (a.aug_eq A) (b.aug_eq B) p _ (wordMap_cells_heq a b p.native f s)

end NativeFiniteView
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
