module
public import ContextualComposition.BinaryAugmentationFubini
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
@[expose] public section
/-! Associativity for the coefficient shuffle at every finite occurrence
length. This is the tensor structure of the comparison, not native
all-arity Fubini or a claim about augmentation transport. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {T : Bi K} {U : C}
variable (M : Middle T U)
def tripleLeft (a b c d e f : C) :=
  K.seq (M.cell (T.obj a b) c (T.obj d e) f)
    (T.map (M.cell a b d e) (K.id (T.obj c f)))
def tripleRight (a b c d e f : C) :=
  K.seq (M.cell a (T.obj b c) d (T.obj e f))
    (T.map (K.id (T.obj a d)) (M.cell b c e f))
def tripleLeftUnit := K.seq M.empty (T.map M.empty (K.id U))
def tripleRightUnit := K.seq M.empty (T.map (K.id U) M.empty)

structure TripleLaw where
  assoc (a b c : C) : K.Hom (T.obj (T.obj a b) c) (T.obj a (T.obj b c))
  assoc_nat {a b c a' b' c' : C}
    (p : K.Hom a a') (q : K.Hom b b') (r : K.Hom c c') :
    K.seq (T.map (T.map p q) r) (assoc a' b' c') =
      K.seq (assoc a b c) (T.map p (T.map q r))
  unit : K.seq (tripleLeftUnit M) (assoc U U U) = tripleRightUnit M
  bin (a b c d e f : C) :
    K.seq (tripleLeft M a b c d e f) (assoc (T.obj a d) (T.obj b e) (T.obj c f)) =
      K.seq (T.map (assoc a b c) (assoc d e f)) (tripleRight M a b c d e f)

variable {X : Type w} (A B D : X → C)
def tripleFoldLeft : (xs : List X) →
    K.Hom (fold T U (fun x => T.obj (T.obj (A x) (B x)) (D x)) xs)
      (T.obj (T.obj (fold T U A xs) (fold T U B xs)) (fold T U D xs))
  | [] => tripleLeftUnit M
  | x::xs => K.seq (T.map (K.id _) (tripleFoldLeft xs))
      (tripleLeft M (A x) (B x) (D x) _ _ _)
def tripleFoldRight : (xs : List X) →
    K.Hom (fold T U (fun x => T.obj (A x) (T.obj (B x) (D x))) xs)
      (T.obj (fold T U A xs) (T.obj (fold T U B xs) (fold T U D xs)))
  | [] => tripleRightUnit M
  | x::xs => K.seq (T.map (K.id _) (tripleFoldRight xs))
      (tripleRight M (A x) (B x) (D x) _ _ _)
theorem triple_fold_assoc (h : TripleLaw M) (xs : List X) :
    K.seq (tripleFoldLeft M A B D xs) (h.assoc _ _ _) =
      K.seq (act T U (fun x => h.assoc (A x) (B x) (D x)) xs) (tripleFoldRight M A B D xs) := by
  induction xs with
  | nil => exact h.unit.trans (K.id_seq _).symm
  | cons x xs ih =>
    simp only [tripleFoldLeft, tripleFoldRight, act, fold, K.assoc, h.bin]
    rw [← K.assoc, ← T.map_seq, K.id_seq, ih, ← K.assoc, ← T.map_seq, K.seq_id]

theorem triple_left_factor (xs : List X) :
    tripleFoldLeft M A B D xs =
      K.seq (shuffle M (fun x => T.obj (A x) (B x)) D xs)
        (T.map (shuffle M A B xs) (K.id (fold T U D xs))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [tripleFoldLeft, fold, shuffle, tripleLeft, ih]
    have hin {a b c : C} (p : K.Hom a b) (q : K.Hom b c) (z : C) :
        T.map (K.seq p q) (K.id z) = K.seq (T.map p (K.id z)) (T.map q (K.id z)) := by
      rw [← T.map_seq, K.id_seq]
    simp only [hin, K.assoc]
    have r :=
      M.nat (K.id (T.obj (A x) (B x))) (K.id (D x))
        (shuffle M A B xs) (K.id (fold T U D xs))
    have hout {a b c : C} (p : K.Hom a b) (q : K.Hom b c) (z : C) :
        T.map (K.id z) (K.seq p q) = K.seq (T.map (K.id z) p) (T.map (K.id z) q) := by
      rw [← T.map_seq, K.id_seq]
    simp only [hout]
    simp only [T.map_id] at r
    simp only [K.assoc]
    congr 1
    rw [← K.assoc, r, K.assoc]
theorem triple_right_factor (xs : List X) :
    tripleFoldRight M A B D xs =
      K.seq (shuffle M A (fun x => T.obj (B x) (D x)) xs)
        (T.map (K.id (fold T U A xs)) (shuffle M B D xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [tripleFoldRight, fold, shuffle, tripleRight, ih]
    have hin {a b c : C} (p : K.Hom a b) (q : K.Hom b c) (z : C) :
        T.map (K.id z) (K.seq p q) = K.seq (T.map (K.id z) p) (T.map (K.id z) q) := by
      rw [← T.map_seq, K.id_seq]
    simp only [hin, K.assoc]
    have r :=
      M.nat (K.id (A x)) (K.id (T.obj (B x) (D x)))
        (K.id (fold T U A xs)) (shuffle M B D xs)
    simp only [T.map_id] at r
    congr 1
    rw [← K.assoc, r, K.assoc]

/-- At arbitrary finite arity (including zero), compares the actual two
ways of iterating the established coefficient shuffle over a three-stage
dependent tensor. -/
theorem occurrence_shuffle_assoc (h : TripleLaw M) (xs : List X) :
    K.seq (K.seq (shuffle M (fun x => T.obj (A x) (B x)) D xs)
        (T.map (shuffle M A B xs) (K.id (fold T U D xs)))) (h.assoc _ _ _) =
    K.seq (act T U (fun x => h.assoc (A x) (B x) (D x)) xs)
      (K.seq (shuffle M A (fun x => T.obj (B x) (D x)) xs)
        (T.map (K.id (fold T U A xs)) (shuffle M B D xs))) := by
  rw [← triple_left_factor, ← triple_right_factor]
  exact triple_fold_assoc M A B D h xs

/-- Collapse the right-associated fold of tensor units, including the
actual empty case (identity), rather than treating the fold as definitionally unit. -/
def unitFold (merge : K.Hom (T.obj U U) U) : (xs : List X) →
    K.Hom (fold T U (fun _ : X => U) xs) U := fun xs =>
  match xs with
  | [] => K.id U
  | _::xs => K.seq (T.map (K.id U) (unitFold merge xs)) merge

/-- The left tensor-unit law for the coefficient shuffle at every occurrence length. -/
theorem occurrence_shuffle_left_unit
    (unit : ∀ a, K.Hom (T.obj U a) a)
    (nullary : K.seq M.empty (unit U) = K.id U)
    (binary : ∀ a b, K.seq (M.cell U a U b)
        (K.seq (T.map (unit U) (K.id (T.obj a b))) (unit (T.obj a b))) =
      T.map (unit a) (unit b))
    (xs : List X) :
    K.seq (shuffle M (fun _ => U) A xs)
      (K.seq (T.map (unitFold (unit U) xs) (K.id (fold T U A xs)))
        (unit (fold T U A xs))) =
      act T U (fun x => unit (A x)) xs := by
  induction xs with
  | nil => simpa only [shuffle, unitFold, fold, act, T.map_id, K.id_seq] using nullary
  | cons x xs ih =>
    simp only [shuffle, unitFold, fold, act, K.assoc]
    have split {a b c : C} (p : K.Hom a b) (q : K.Hom b c) (z : C) :
        T.map (K.seq p q) (K.id z) = K.seq (T.map p (K.id z)) (T.map q (K.id z)) := by
      rw [← T.map_seq, K.id_seq]
    have r := M.nat (K.id U) (K.id (A x)) (unitFold (unit U) xs) (K.id (fold T U A xs))
    simp only [T.map_id] at r
    simp only [split, K.assoc]
    rw [← K.assoc (M.cell _ _ _ _) (T.map _ _), ← r]
    simp only [K.assoc]
    rw [binary, ← T.map_seq, K.id_seq, ← T.map_seq, K.id_seq, ih]

/-- The right tensor-unit law for the coefficient shuffle at every occurrence length. -/
theorem occurrence_shuffle_right_unit
    (unit : ∀ a, K.Hom (T.obj a U) a)
    (nullary : K.seq M.empty (unit U) = K.id U)
    (binary : ∀ a b, K.seq (M.cell a U b U)
        (K.seq (T.map (K.id (T.obj a b)) (unit U)) (unit (T.obj a b))) =
      T.map (unit a) (unit b))
    (xs : List X) :
    K.seq (shuffle M A (fun _ => U) xs)
      (K.seq (T.map (K.id (fold T U A xs)) (unitFold (unit U) xs))
        (unit (fold T U A xs))) =
      act T U (fun x => unit (A x)) xs := by
  induction xs with
  | nil => simpa only [shuffle, unitFold, fold, act, T.map_id, K.id_seq] using nullary
  | cons x xs ih =>
    simp only [shuffle, unitFold, fold, act, K.assoc]
    have split {a b c : C} (p : K.Hom a b) (q : K.Hom b c) (z : C) :
        T.map (K.id z) (K.seq p q) = K.seq (T.map (K.id z) p) (T.map (K.id z) q) := by
      rw [← T.map_seq, K.id_seq]
    have r := M.nat (K.id (A x)) (K.id U) (K.id (fold T U A xs)) (unitFold (unit U) xs)
    simp only [T.map_id] at r
    simp only [split, K.assoc]
    rw [← K.assoc (M.cell _ _ _ _) (T.map _ _), ← r]
    simp only [K.assoc]
    rw [binary, ← T.map_seq, K.id_seq, ← T.map_seq, K.id_seq, ih]
end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The coefficient shuffle associator law is induced by the actual
braiding, unitors and associator, not a new hypothesis on a standard rig. -/
def standardTripleLaw : TripleLaw (additiveMiddle (Additive.ofBraided (C:=C))) where
  assoc a b c := (α_ a b c).hom
  assoc_nat p q r := associator_naturality p q r
  unit := by
    change ((λ_ (𝟙_ C)).inv ≫ ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (𝟙_ C))) ≫
        (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom =
      (λ_ (𝟙_ C)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ (λ_ (𝟙_ C)).inv)
    monoidal
  bin a b c d e f := by
    change (tensorμ (a ⊗ b) c (d ⊗ e) f ≫ (tensorμ a b d e ⊗ₘ 𝟙 (c ⊗ f))) ≫
        (α_ (a ⊗ d) (b ⊗ e) (c ⊗ f)).hom =
      ((α_ a b c).hom ⊗ₘ (α_ d e f).hom) ≫
        tensorμ a (b ⊗ c) d (e ⊗ f) ≫ (𝟙 (a ⊗ d) ⊗ₘ tensorμ b c e f)
    simpa only [Category.assoc, id_tensorHom, tensorHom_id] using associator_monoidal a b c d e f

local notation "Mstd" => additiveMiddle (Additive.ofBraided (C:=C))
local notation "Tstd" => binary (Binary.ofMonoidal (C:=C))
universe w
variable {X : Type w} (A : X → C)

theorem standard_occurrence_shuffle_left_unit (xs : List X) :
    shuffle Mstd (fun _ => 𝟙_ C) A xs ≫
      ((unitFold (T:=Tstd) (λ_ (𝟙_ C)).hom xs) ⊗ₘ (𝟙 (fold Tstd (𝟙_ C) A xs))) ≫
        (λ_ (fold Tstd (𝟙_ C) A xs)).hom =
      act Tstd (𝟙_ C) (fun x => (λ_ (A x)).hom) xs := by
  refine occurrence_shuffle_left_unit Mstd A (fun a => (λ_ a).hom) ?_ ?_ xs
  · change (λ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
    monoidal
  · intro a b
    change tensorμ (𝟙_ C) a (𝟙_ C) b ≫
      (((λ_ (𝟙_ C)).hom) ⊗ₘ (𝟙 (a ⊗ b))) ≫ (λ_ (a ⊗ b)).hom = (λ_ a).hom ⊗ₘ (λ_ b).hom
    simpa only [tensorHom_id] using (leftUnitor_monoidal a b).symm

theorem standard_occurrence_shuffle_right_unit (xs : List X) :
    shuffle Mstd A (fun _ => 𝟙_ C) xs ≫
      ((𝟙 (fold Tstd (𝟙_ C) A xs)) ⊗ₘ (unitFold (T:=Tstd) (ρ_ (𝟙_ C)).hom xs)) ≫
        (ρ_ (fold Tstd (𝟙_ C) A xs)).hom =
      act Tstd (𝟙_ C) (fun x => (ρ_ (A x)).hom) xs := by
  refine occurrence_shuffle_right_unit Mstd A (fun a => (ρ_ a).hom) ?_ ?_ xs
  · change (λ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
    monoidal
  · intro a b
    change tensorμ a (𝟙_ C) b (𝟙_ C) ≫
      ((𝟙 (a ⊗ b)) ⊗ₘ ((ρ_ (𝟙_ C)).hom)) ≫ (ρ_ (a ⊗ b)).hom = (ρ_ a).hom ⊗ₘ (ρ_ b).hom
    rw [show (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom by monoidal]
    simpa only [id_tensorHom] using (rightUnitor_monoidal a b).symm

omit [BraidedCategory C] in
theorem occurrence_act_id (A : X → C) (xs : List X) :
    act Tstd (𝟙_ C) (fun x => 𝟙 (A x)) xs = 𝟙 (fold Tstd (𝟙_ C) A xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [act, ih]
    exact (Tstd).map_id _ _

variable (C)

/-- The pointwise morphisms vary freely at each input address. Changing
the list itself is not a morphism of this fixed-list domain. -/
def orderedFold (xs : List X) : (Discrete X ⥤ C) ⥤ C where
  obj F := fold Tstd (𝟙_ C) (fun x => F.obj (.mk x)) xs
  map p := act Tstd (𝟙_ C) (fun x => p.app (.mk x)) xs
  map_id F := occurrence_act_id (fun x => F.obj (.mk x)) xs
  map_comp p q := (act_seq Tstd (𝟙_ C) (fun x => p.app (.mk x)) (fun x => q.app (.mk x)) xs).symm



set_option backward.isDefEq.respectTransparency false in
instance orderedFoldOplax (xs : List X) : (orderedFold C xs).OplaxMonoidal where
  η := unitFold (T:=Tstd) (λ_ (𝟙_ C)).hom xs
  δ F G := shuffle Mstd (fun x => F.obj (.mk x)) (fun x => G.obj (.mk x)) xs
  δ_natural_left {F H} p G := by
    let A : X → C := fun x => F.obj (.mk x)
    let B : X → C := fun x => G.obj (.mk x)
    let A' : X → C := fun x => H.obj (.mk x)
    let q : ∀ x, A x ⟶ A' x := fun x => p.app (.mk x)
    have h : act Tstd (𝟙_ C) (fun x => q x ⊗ₘ 𝟙 (B x)) xs ≫ shuffle Mstd A' B xs =
        shuffle Mstd A B xs ≫
          (act Tstd (𝟙_ C) q xs ⊗ₘ act Tstd (𝟙_ C) (fun x => 𝟙 (B x)) xs) :=
      shuffle_nat Mstd q (fun x => 𝟙 (B x)) xs
    have e : (fun x => q x ⊗ₘ 𝟙 (B x)) = (fun x => (p ▷ G).app (.mk x)) := funext (fun x => tensorHom_id _ _)
    rw [occurrence_act_id, e] at h
    rw [← tensorHom_id]
    exact h.symm
  δ_natural_right {G H} F p := by
    let A : X → C := fun x => F.obj (.mk x)
    let B : X → C := fun x => G.obj (.mk x)
    let B' : X → C := fun x => H.obj (.mk x)
    let q : ∀ x, B x ⟶ B' x := fun x => p.app (.mk x)
    have h : act Tstd (𝟙_ C) (fun x => 𝟙 (A x) ⊗ₘ q x) xs ≫ shuffle Mstd A B' xs =
        shuffle Mstd A B xs ≫
          (act Tstd (𝟙_ C) (fun x => 𝟙 (A x)) xs ⊗ₘ act Tstd (𝟙_ C) q xs) :=
      shuffle_nat Mstd (fun x => 𝟙 (A x)) q xs
    have e : (fun x => 𝟙 (A x) ⊗ₘ q x) = (fun x => (F ◁ p).app (.mk x)) := funext (fun x => id_tensorHom _ _)
    rw [occurrence_act_id, e] at h
    rw [← id_tensorHom]
    exact h.symm
  oplax_associativity F G H := by
    rw [← tensorHom_id, ← id_tensorHom, ← Category.assoc]
    exact occurrence_shuffle_assoc Mstd (fun x => F.obj (.mk x)) (fun x => G.obj (.mk x))
      (fun x => H.obj (.mk x)) standardTripleLaw xs
  oplax_left_unitality F := by
    rw [← cancel_mono (λ_ ((orderedFold C xs).obj F)).hom]
    simp only [Iso.inv_hom_id, Category.assoc]
    have H := standard_occurrence_shuffle_left_unit (fun x => F.obj (.mk x)) xs
    rw [← tensorHom_id]
    exact (((orderedFold C xs).map_comp (λ_ F).inv (λ_ F).hom).symm.trans
      (by rw [Iso.inv_hom_id, Functor.map_id])).symm.trans
      (congrArg (fun p => (orderedFold C xs).map (λ_ F).inv ≫ p) H.symm)
  oplax_right_unitality F := by
    rw [← cancel_mono (ρ_ ((orderedFold C xs).obj F)).hom]
    simp only [Iso.inv_hom_id, Category.assoc]
    have H := standard_occurrence_shuffle_right_unit (fun x => F.obj (.mk x)) xs
    have h : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by monoidal
    rw [← id_tensorHom, ← h]
    exact (((orderedFold C xs).map_comp (ρ_ F).inv (ρ_ F).hom).symm.trans
      (by rw [Iso.inv_hom_id, Functor.map_id])).symm.trans
      (congrArg (fun p => (orderedFold C xs).map (ρ_ F).inv ≫ p) H.symm)


open Functor.OplaxMonoidal

instance orderedFoldCounitIso (xs : List X) : IsIso (η (orderedFold C xs)) := by
  change IsIso (unitFold (T:=Tstd) (λ_ (𝟙_ C)).hom xs)
  induction xs with
  | nil =>
    change IsIso (𝟙 (𝟙_ C))
    infer_instance
  | cons x xs ih =>
    change IsIso ((𝟙 (𝟙_ C) ⊗ₘ unitFold (T:=Tstd) (λ_ (𝟙_ C)).hom xs) ≫
      (λ_ (𝟙_ C)).hom)
    infer_instance

instance orderedFoldCotensorIso (xs : List X) (F G : Discrete X ⥤ C) :
    IsIso (δ (orderedFold C xs) F G) := by
  let i := shuffleInv (additiveMiddleInv (Additive.ofBraided (C:=C)))
    (fun x : X => F.obj (.mk x)) (fun x => G.obj (.mk x)) xs
  exact ⟨i.inv, i.hi, i.ih⟩

/-- Pointwise coefficient variation for a fixed ordered list of addresses
is strong monoidal for the actual recursive occurrence comparison. -/
noncomputable instance orderedFoldMonoidal (xs : List X) : (orderedFold C xs).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (orderedFold C xs)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
