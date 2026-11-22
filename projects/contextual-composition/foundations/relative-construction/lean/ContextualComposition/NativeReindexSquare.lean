module
public import ContextualComposition.NativeBinaryAugIso

@[expose] public section
/-! Naturality reductions in the actual native category. These do not
supply the missing independent/dependent functor maps; they expose the
exact fibrewise equality those maps must satisfy. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

theorem fibreList_postequiv {n m l : Nat} (f : Fin n → Fin m) (e : Fin m ≃ Fin l) (j : Fin l) :
    fibreList (e ∘ f) j = fibreList f (e.symm j) := by
  unfold fibreList
  apply congrArg (fun p => (List.finRange n).filter p)
  funext x
  have E : e (f x) = j ↔ f x = e.symm j := by
    rw [← e.apply_symm_apply j, e.apply_eq_iff_eq, e.symm_apply_apply]
  change (e (f x) == j) = (f x == e.symm j)
  simp only [beq_eq_decide]
  simp only [E]

set_option backward.isDefEq.respectTransparency false in
theorem reindexSingleton_natural {n m : Nat} (e : Fin n ≃ Fin m) {A B : Fin n → C}
    (p : ∀ x, A x ⟶ B x) (j : Fin m) :
    standardPushMap e p j ≫ reindexSingleton e B j =
      reindexSingleton e A j ≫ p (e.symm j) := by
  have aux (ls : List (Fin n)) (E : ls = [e.symm j]) :
      act 𝒮 Z p ls ≫ eqToHom (congrArg (fold 𝒮 Z B) E) ≫ (ρ_ (B (e.symm j))).hom =
        (eqToHom (congrArg (fold 𝒮 Z A) E) ≫ (ρ_ (A (e.symm j))).hom) ≫ p (e.symm j) := by
    subst ls
    simp only [eqToHom_refl, Category.id_comp, act]
    change (p (e.symm j) ⊗ₘ 𝟙 Z) ≫ (ρ_ (B (e.symm j))).hom =
      (ρ_ (A (e.symm j))).hom ≫ p (e.symm j)
    rw [tensorHom_id, rightUnitor_naturality]
  exact aux _ (equiv_fibreList e j)

set_option backward.isDefEq.respectTransparency false in
theorem standardPush_postequiv_split {n m l : Nat} (f : Fin n → Fin m) (e : Fin m ≃ Fin l)
    (A : Fin n → C) (j : Fin l) :
    standardPushSplit f e A j ≫ reindexSingleton e (standardPushObj f A) j =
    eqToHom (congrArg (fold 𝒮 Z A) (fibreList_postequiv f e j)) := by
  let k := e.symm j
  let h : fibreList e j = [k] := equiv_fibreList e j
  let a : fibreList (e ∘ f) j = fibreList f k := fibreList_postequiv f e j
  let b : fibreList f k = ([k] : List (Fin m)).flatMap (fibreList f) :=
    (List.append_nil _).symm
  let d : ([k] : List (Fin m)).flatMap (fibreList f) = (fibreList e j).flatMap (fibreList f) :=
    congrArg (fun l => l.flatMap (fibreList f)) h.symm
  rw [standardPushSplit_choice _ _ _ _ (castOrder (a.trans (b.trans d))), castOrder_map]
  have aux (ys : List (Fin m)) (h : ys = [k]) :
      (eqToHom (congrArg (fold 𝒮 Z A)
          (a.trans (b.trans (congrArg (fun l => l.flatMap (fibreList f)) h.symm)))) ≫
        rowsChart A (fibreList f) ys) ≫
        (eqToHom (congrArg (fold 𝒮 Z (standardPushObj f A)) h) ≫
          (ρ_ (standardPushObj f A k)).hom) = eqToHom (congrArg (fold 𝒮 Z A) a) := by
    subst ys
    let E := congrArg (fold 𝒮 Z A) a
    let B := congrArg (fold 𝒮 Z A) b
    change (eqToHom (E.trans B) ≫ rowsChart A (fibreList f) [k]) ≫
      (𝟙 _ ≫ (ρ_ (standardPushObj f A k)).hom) = eqToHom E
    rw [← eqToHom_trans E B, Category.id_comp]
    simp only [Category.assoc]
    have t := rowsChart_one A (fibreList f) k
    change eqToHom B ≫ rowsChart A (fibreList f) [k] ≫ (ρ_ (standardPushObj f A k)).hom =
      𝟙 (standardPushObj f A k) at t
    have h := congrArg (fun m => eqToHom E ≫ m) t
    exact h.trans (Category.comp_id _)
  exact aux _ h

set_option backward.isDefEq.respectTransparency false in
theorem standardPush_postequiv_collapse {n m l : Nat} (f : Fin n → Fin m) (e : Fin m ≃ Fin l)
    {A : Fin n → C} {B : Fin m → C} {D : Fin l → C}
    (p : ∀ i, standardPushObj f A i ⟶ B i) (q : ∀ j, B (e.symm j) ⟶ D j) (j : Fin l) :
    standardPushSplit f e A j ≫ (standardPushMap e p j ≫ reindexSingleton e B j ≫ q j) =
      eqToHom (congrArg (fold 𝒮 Z A) (fibreList_postequiv f e j)) ≫ p (e.symm j) ≫ q j := by
  rw [← Category.assoc (standardPushMap e p j), reindexSingleton_natural]
  simp only [Category.assoc]
  rw [← Category.assoc (standardPushSplit f e A j)]
  exact congrArg (fun k => k ≫ p (e.symm j) ≫ q j) (standardPush_postequiv_split f e A j)

theorem fibreList_preequiv_perm {n m l : Nat} (e : Fin n ≃ Fin m) (f : Fin m → Fin l) (j : Fin l) :
    (fibreList (f ∘ e) j).Perm ((fibreList f j).map e.symm) := by
  have h : ((fibreList f j).map e.symm).Nodup :=
    (fibreList_nodup f j).map e.symm (fun _ _ h h' => h (e.symm.injective h'))
  apply (List.perm_ext_iff_of_nodup (fibreList_nodup _ _) h).mpr
  intro x
  simp only [mem_fibreList, Function.comp_apply, List.mem_map]
  constructor
  · intro h
    exact ⟨e x, h, e.symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [e.apply_symm_apply]

noncomputable def fibreList_preequiv_order {n m l : Nat} (e : Fin n ≃ Fin m) (f : Fin m → Fin l) (j : Fin l) :
    AddressOrder (Fin n) (fibreList (f ∘ e) j) ((fibreList f j).map e.symm) :=
  Classical.choice (AddressOrder.ofPerm (fibreList_preequiv_perm e f j))

set_option backward.isDefEq.respectTransparency false in
theorem native_hom_iff_cell {A B : Family C} {f g : Fin A.n → Fin B.n}
    (e : f = g) (p : ∀ j, standardPushObj f A.val j ⟶ B.val j)
    (q : ∀ j, standardPushObj g A.val j ⟶ B.val j) :
    (Hom.mk f p : Hom ℙ A B) = Hom.mk g q ↔
      (∀ j, p j = eqToHom (congrArg (fun k => standardPushObj k A.val j) e) ≫ q j) := by
  constructor
  · intro h j
    subst g
    have t := congrFun (eq_of_heq (Hom.mk.inj h).2) j
    simpa only [eqToHom_refl, Category.id_comp] using t
  · exact native_hom_ext e p q

set_option backward.isDefEq.respectTransparency false in
/-- Exact fibre criterion for a carrier-changing square between actual
native arrows and carrier-equivalence comparisons. The side arrows can
have arbitrary noninjective carriers and opaque empty-fibre cells. -/
theorem native_reindex_square_iff {A A' B B' : Family C} (p : Hom ℙ A B) (q : Hom ℙ A' B')
    (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n)
    (α : ∀ j, A.val (e.symm j) ≅ A'.val j) (β : ∀ j, B.val (d.symm j) ≅ B'.val j)
    (h : (d : Fin B.n → Fin B'.n) ∘ p.addr = q.addr ∘ e) :
    p.comp (nativeReindex d β) = (nativeReindex e α).comp q ↔ ∀ j,
      eqToHom (congrArg (fold 𝒮 Z A.val) (fibreList_postequiv p.addr d j)) ≫
          p.cell (d.symm j) ≫ (β j).hom =
      eqToHom (congrArg (fun f => standardPushObj f A.val j) h) ≫
        AddressOrder.mapSum additiveStructure A.val (fibreList_preequiv_order e q.addr j) ≫
          eqToHom (std_fold_map A.val e.symm (fibreList q.addr j)) ≫
            standardPushMap q.addr (fun k => (α k).hom) j ≫ q.cell j := by
  refine (native_hom_iff_cell h _ _).trans ?_
  constructor <;> intro H j <;> specialize H j
  all_goals
    have u := standardPush_postequiv_collapse p.addr d p.cell (fun k => (β k).hom) j
    have l := standardPush_equiv_collapse e q.addr A.val A'.val (fun k => (α k).hom) j
      (fibreList_preequiv_order e q.addr j)
    let a (k : Fin A'.n) := reindexSingleton e A.val k ≫ (α k).hom
    let b (k : Fin B'.n) := reindexSingleton d B.val k ≫ (β k).hom
    let F := eqToHom (congrArg (fun f => standardPushObj f A.val j) h)
    have U : standardPushSplit p.addr d A.val j ≫ standardPushMap d p.cell j ≫ b j =
        eqToHom (congrArg (fold 𝒮 Z A.val) (fibreList_postequiv p.addr d j)) ≫
          p.cell (d.symm j) ≫ (β j).hom := u
    have L := congrArg (fun t => F ≫ t ≫ q.cell j) l
    simp only [Category.assoc] at L
    first
    | change standardPushSplit p.addr d A.val j ≫ standardPushMap d p.cell j ≫ b j =
        F ≫ standardPushSplit e q.addr A.val j ≫ standardPushMap q.addr a j ≫ q.cell j at H
      exact U.symm.trans (H.trans L)
    | change standardPushSplit p.addr d A.val j ≫ standardPushMap d p.cell j ≫ b j =
        F ≫ standardPushSplit e q.addr A.val j ≫ standardPushMap q.addr a j ≫ q.cell j
      exact U.trans (H.trans L.symm)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
