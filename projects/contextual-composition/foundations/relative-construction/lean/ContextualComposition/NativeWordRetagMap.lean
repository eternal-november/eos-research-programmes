module
public import ContextualComposition.NativeOrderedFubini
@[expose] public section

/-! Ordered retagging of an actual native map. This is not a permutation
of positions, and it preserves the whole cell at the same final address. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w x y z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {X Y U V : Type u} [DecidableEq Y] [DecidableEq V]
variable (r : X ≃ U) (s : Y ≃ V) (f : X → Y) (g : U → V)
variable (coh : ∀ x, s (f x) = g (r x))
variable {xs : List X} {ys : List Y} {us : List U} {vs : List V}
variable (eu : xs.map r = us) (ev : ys.map s = vs)

include coh in
theorem retag_wordFibre (i : Y) :
    (wordFibre xs f i).map r = wordFibre (xs.map r) g (s i) := by
  unfold wordFibre
  rw [List.filter_map]
  apply congrArg (List.map (r : X → U))
  apply List.filter_congr
  intro x _
  simp only [Function.comp_apply, ← coh x, s.injective.eq_iff]

include coh eu ev in
omit [DecidableEq Y] [DecidableEq V] in
theorem retag_word_support (h : ∀ x ∈ xs, f x ∈ ys) :
    ∀ u ∈ us, g u ∈ vs := by
  intro u hu
  rw [← eu] at hu
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hu
  rw [← coh x, ← ev]
  exact List.mem_map.mpr ⟨f x,h x hx,rfl⟩

variable (A : U → C) (B : V → C)
variable (p : ∀ i ∈ ys, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C)
    (A ∘ r) (wordFibre xs f i) ⟶ B (s i))

def retagWordCell (j : V) (hj : j ∈ vs) :
    fold 𝒮 Zₐ A (wordFibre us g j) ⟶ B j :=
  let i := s.symm j
  let h₀ : i ∈ ys := by
    have h : j ∈ ys.map s := ev.symm ▸ hj
    obtain ⟨k,hk,e⟩ := List.mem_map.mp h
    subst j
    change s.symm (s k) ∈ ys
    rw [s.symm_apply_apply]
    exact hk
  let e : (wordFibre xs f i).map r = wordFibre us g j :=
    (retag_wordFibre r s f g coh i).trans (congrArg₂ (fun x y => wordFibre x g y) eu (s.apply_symm_apply j))
  let pin := ((congrArg (fold 𝒮 Zₐ A) e.symm).trans (std_fold_map A r (wordFibre xs f i)))
  eqToHom pin ≫ p i h₀ ≫ eqToHom (congrArg B (s.apply_symm_apply j))

set_option backward.isDefEq.respectTransparency false in
theorem retagWordCell_heq (i : Y) (hi : i ∈ ys) (hj : s i ∈ vs) :
    HEq (retagWordCell r s f g coh eu ev A B p (s i) hj) (p i hi) := by
  unfold retagWordCell
  dsimp only
  refine (hom_source_pin_heq _ _).trans ?_
  refine (hom_target_pin_heq _ _).trans ?_
  have h {i' : Y} (e : i' = i) (h' : i' ∈ ys) : HEq (p i' h') (p i hi) := by subst i'; rfl
  exact h (s.symm_apply_apply i) _

set_option backward.isDefEq.respectTransparency false in
theorem retagWordMap_heq (hs : ∀ x ∈ xs, f x ∈ ys) (ht : ys.Nodup) (hv : vs.Nodup) :
    HEq (wordNativeMap f hs ht (A ∘ r) (B ∘ s) (fun i => p ys[i] (List.getElem_mem _)))
      (wordNativeMap g (retag_word_support r s f g coh eu ev hs) hv A B
        (fun j => retagWordCell r s f g coh eu ev A B p vs[j] (List.getElem_mem _))) := by
  apply readWordNativeMap_heq A B r s f g hs (retag_word_support r s f g coh eu ev hs) ht hv eu ev
    (fun x _ => coh x)
  intro i
  let j := Fin.cast ((List.length_map (s : Y → V)).symm.trans (congrArg List.length ev)) i
  let q := retagWordCell r s f g coh eu ev A B p
  have a : s ys[i] = vs[j] := retag_word_get s ys ev i
  let h' : s ys[i] ∈ vs := a.symm ▸ List.getElem_mem _
  have e {i j : V} (a : i = j) (hi : i ∈ vs) (hj : j ∈ vs) : HEq (q i hi) (q j hj) := by subst j; rfl
  exact (retagWordCell_heq r s f g coh eu ev A B p ys[i] (List.getElem_mem _) h').symm.trans
    (e a h' (List.getElem_mem _))

set_option backward.isDefEq.respectTransparency false in
theorem wordNativeMap_identChart_square
    {X Y : Type u} [DecidableEq Y] {xs : List X} {ys : List Y}
    (f : X → Y) (hs : ∀ x ∈ xs, f x ∈ ys)
    (hx : xs.Nodup) (hy : ys.Nodup)
    (A A' : X → C) (B B' : Y → C)
    (α : ∀ x, A x ≅ A' x) (β : ∀ y, B y ≅ B' y)
    (p : ∀ y ∈ ys, fold 𝒮 Zₐ A (wordFibre xs f y) ⟶ B y)
    (q : ∀ y ∈ ys, fold 𝒮 Zₐ A' (wordFibre xs f y) ⟶ B' y)
    (h : ∀ y (hy : y ∈ ys), p y hy ≫ (β y).hom =
      act 𝒮 Zₐ (fun x => (α x).hom) (wordFibre xs f y) ≫ q y hy) :
    (wordNativeMap f hs hy A B (fun i => p ys[i] (List.getElem_mem _))).comp
        (nativeReindex (A:=wordFamily B ys) (B:=wordFamily B' ys) (wordEquiv (AddressOrder.ident ys).perm hy) (wordComparisonCells B B' (.ident ys) hy β)) =
      (nativeReindex (A:=wordFamily A xs) (B:=wordFamily A' xs) (wordEquiv (AddressOrder.ident xs).perm hx) (wordComparisonCells A A' (.ident xs) hx α)).comp
        (wordNativeMap f hs hy A' B' (fun i => q ys[i] (List.getElem_mem _))) := by
  apply (wordNativeMap_square_iff A A' B B' (.ident xs) (.ident ys) hx hy hs hs α β p q).mpr
  intro j
  let k := ys[j]
  let w := wordFibre xs f k
  have e := tagged_permutation_coherent A (hx.filter _) (wordFibreOrder f (.ident xs) k) (.ident w)
  change AddressOrder.mapSum additiveStructure A (wordFibreOrder f (.ident xs) k) = 𝟙 _ at e
  rw [e, Category.id_comp]
  exact h k (List.getElem_mem _)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
