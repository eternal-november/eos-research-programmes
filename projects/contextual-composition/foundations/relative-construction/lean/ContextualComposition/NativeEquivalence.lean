module
public import ContextualComposition.StandardNativePush

@[expose] public section
/-! Native isomorphisms over actual equivalences of finite carriers.
The inverse is computed with the actual direct-image comparisons. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

set_option backward.isDefEq.respectTransparency false in
theorem standardPushMap_iso {n m : Nat} (f : Fin n → Fin m) {A B : Fin n → C}
    (p : ∀ i, A i ⟶ B i) (hp : ∀ i, IsIso (p i)) (j : Fin m) :
    IsIso (standardPushMap f p j) := by
  let _ (i : Fin n) := hp i
  let q : ∀ i, B i ⟶ A i := fun i => inv (p i)
  refine ⟨standardPushMap f q j, ?_, ?_⟩
  · rw [← standardPushMap_comp]
    have e : (fun i => p i ≫ q i) = fun i => 𝟙 (A i) := by
      funext i
      exact IsIso.hom_inv_id (p i)
    rw [e, standardPushMap_id]
  · rw [← standardPushMap_comp]
    have e : (fun i => q i ≫ p i) = fun i => 𝟙 (B i) := by
      funext i
      exact IsIso.inv_hom_id (p i)
    rw [e, standardPushMap_id]

set_option backward.isDefEq.respectTransparency false in
theorem native_hom_ext {A B : Family C} {f g : Fin A.n → Fin B.n}
    (e : f = g) (p : ∀ j, standardPushObj f A.val j ⟶ B.val j)
    (q : ∀ j, standardPushObj g A.val j ⟶ B.val j)
    (h : ∀ j, p j = eqToHom (congrArg (fun k => standardPushObj k A.val j) e) ≫ q j) :
    (Hom.mk f p : Hom ℙ A B) = Hom.mk g q := by
  subst g
  apply congrArg (Hom.mk f)
  funext j
  simpa only [eqToHom_refl, Category.id_comp] using h j

theorem equiv_fibreList {n m : Nat} (e : Fin n ≃ Fin m) (j : Fin m) :
    fibreList e j = [e.symm j] := by
  have h : e.symm j ∈ fibreList e j := mem_fibreList.mpr (e.apply_symm_apply j)
  rcases w : fibreList e j with _ | ⟨x,xs⟩
  · simp [w] at h
  · have k : e x = j := mem_fibreList.mp (w.symm ▸ List.mem_cons_self)
    have k' : x = e.symm j := (congrArg e.symm k).symm ▸ (e.symm_apply_apply x).symm
    subst x
    congr 1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have ha' : e a = j := mem_fibreList.mp (w.symm ▸ List.mem_cons_of_mem _ ha)
    have eq : a = e.symm j := e.injective (ha'.trans (e.apply_symm_apply j).symm)
    subst a
    exact (List.nodup_cons.mp (w ▸ fibreList_nodup e j)).1 ha

def reindexSingleton {n m : Nat} (e : Fin n ≃ Fin m) (A : Fin n → C) (j : Fin m) :
    standardPushObj e A j ⟶ A (e.symm j) :=
  eqToHom (congrArg (fold 𝒮 Z A) (equiv_fibreList e j)) ≫ (ρ_ (A (e.symm j))).hom

instance reindexSingletonIso {n m : Nat} (e : Fin n ≃ Fin m) (A : Fin n → C) (j : Fin m) :
    IsIso (reindexSingleton e A j) := by
  let k : standardPushObj e A j = A (e.symm j) ⊗ Z := congrArg (fold 𝒮 Z A) (equiv_fibreList e j)
  change IsIso (eqToHom k ≫ (ρ_ (A (e.symm j))).hom)
  infer_instance

/-- The actual native arrow over a carrier equivalence and given
coefficient isomorphisms. The native cell first uses its literal whole
singleton preimage, not an assumed equality of coefficient objects. -/
noncomputable def nativeReindex {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (φ : ∀ j, A.val (e.symm j) ≅ B.val j) : Hom ℙ A B :=
  ⟨e, fun j => reindexSingleton e A.val j ≫ (φ j).hom⟩


set_option backward.isDefEq.respectTransparency false in
theorem native_equiv_cancel {A B D : Family C} (e : Fin A.n ≃ Fin B.n)
    (p : ∀ j, standardPushObj e A.val j ⟶ B.val j) (hp : ∀ j, IsIso (p j))
    {u v : Hom ℙ B D} (H : Hom.comp (Hom.mk e p) u = Hom.comp (Hom.mk e p) v) : u = v := by
  have E (j : Fin B.n) : u.addr j = v.addr j := by
    have h := congrArg (fun t : Hom ℙ A D => t.addr (e.symm j)) H
    change u.addr (e (e.symm j)) = v.addr (e (e.symm j)) at h
    rw [e.apply_symm_apply] at h
    exact h
  cases u with
  | mk g a =>
    cases v with
    | mk k b =>
      have e₁ : g = k := funext E
      subst k
      apply congrArg (Hom.mk g)
      have h : (fun j => standardPushSplit e g A.val j ≫ (standardPushMap g p j ≫ a j)) =
          fun j => standardPushSplit e g A.val j ≫ (standardPushMap g p j ≫ b j) :=
        eq_of_heq (Hom.mk.inj H).2
      funext j
      let _ : IsIso (standardPushMap g p j) := standardPushMap_iso g p hp j
      exact (cancel_epi (standardPushMap g p j)).mp
        ((cancel_epi (standardPushSplit e g A.val j)).mp (congrFun h j))

theorem equiv_symm_comp {n m : Nat} (e : Fin n ≃ Fin m) : (e.symm : Fin m → Fin n) ∘ e = id :=
  funext e.symm_apply_apply

set_option backward.isDefEq.respectTransparency false in
noncomputable def nativeEquivInv {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (p : ∀ j, standardPushObj e A.val j ⟶ B.val j) (hp : ∀ j, IsIso (p j)) : Hom ℙ B A where
  addr := e.symm
  cell j :=
    let _ : IsIso (standardPushMap e.symm p j) := standardPushMap_iso e.symm p hp j
    inv (standardPushSplit e e.symm A.val j ≫ standardPushMap e.symm p j) ≫
      eqToHom (congrArg (fun k => standardPushObj k A.val j) (equiv_symm_comp e)) ≫
        standardPushSingle A.val j

set_option backward.isDefEq.respectTransparency false in
theorem nativeEquivInv_right {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (p : ∀ j, standardPushObj e A.val j ⟶ B.val j) (hp : ∀ j, IsIso (p j)) :
    Hom.comp (Hom.mk e p) (nativeEquivInv e p hp) = Hom.ident A := by
  apply native_hom_ext (equiv_symm_comp e)
  intro j
  let _ : IsIso (standardPushMap e.symm p j) := standardPushMap_iso e.symm p hp j
  change standardPushSplit e e.symm A.val j ≫
    (standardPushMap e.symm p j ≫
      inv (standardPushSplit e e.symm A.val j ≫ standardPushMap e.symm p j) ≫ _) = _
  rw [← Category.assoc, IsIso.hom_inv_id_assoc]
  rfl

theorem nativeEquivInv_left {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (p : ∀ j, standardPushObj e A.val j ⟶ B.val j) (hp : ∀ j, IsIso (p j)) :
    Hom.comp (nativeEquivInv e p hp) (Hom.mk e p) = Hom.ident B := by
  apply native_equiv_cancel e p hp
  rw [← Hom.comp_assoc, nativeEquivInv_right, Hom.ident_comp, Hom.comp_ident]


structure NativeFamilyIso (A B : Family C) where
  hom : Hom ℙ A B
  inv : Hom ℙ B A
  hom_inv : hom.comp inv = Hom.ident A
  inv_hom : inv.comp hom = Hom.ident B

noncomputable def nativeReindexIso {A B : Family C} (e : Fin A.n ≃ Fin B.n)
    (φ : ∀ j, A.val (e.symm j) ≅ B.val j) : NativeFamilyIso A B := by
  let p (j : Fin B.n) := reindexSingleton e A.val j ≫ (φ j).hom
  let hp (j : Fin B.n) : IsIso (p j) := by unfold p; infer_instance
  exact ⟨nativeReindex e φ, nativeEquivInv e p hp, nativeEquivInv_right e p hp,
    nativeEquivInv_left e p hp⟩

structure NativeAugmentedIso {I : C} (A B : Aug ℙ I) where
  hom : AugHom ℙ A B
  inv : AugHom ℙ B A
  hom_inv : hom.comp inv = AugHom.ident A
  inv_hom : inv.comp hom = AugHom.ident B

/-- An augmented isomorphism needs only the forward preservation proof;
the inverse preserves the same actual terminal map by cancellation. -/
def NativeFamilyIso.augment {I : C} {A B : Aug ℙ I}
    (e : NativeFamilyIso A.base B.base) (p : e.hom.comp B.ε = A.ε) :
    NativeAugmentedIso A B where
  hom := ⟨e.hom,p⟩
  inv := ⟨e.inv, by
    rw [← p, ← Hom.comp_assoc, e.inv_hom, Hom.ident_comp]⟩
  hom_inv := AugHom.ext e.hom_inv
  inv_hom := AugHom.ext e.inv_hom

/-- A literal native augmented comparison over a given carrier equivalence.
The equality input is the actual terminal composite, not a pointwise
preservation predicate on coefficient labels. -/
noncomputable def nativeReindexAugIso {I : C} {A B : Aug ℙ I}
    (e : Fin A.base.n ≃ Fin B.base.n) (φ : ∀ j, A.base.val (e.symm j) ≅ B.base.val j)
    (p : (nativeReindex e φ).comp B.ε = A.ε) :
    NativeAugmentedIso A B :=
  (nativeReindexIso e φ).augment p

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
