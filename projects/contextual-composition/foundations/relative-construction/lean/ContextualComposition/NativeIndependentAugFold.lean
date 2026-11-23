module
public import ContextualComposition.NativeBinaryFunctoriality
@[expose] public section

/-! The independent ordered product on the actual augmented native families. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

noncomputable def totalNativeCell {I : C} (A : Aug ℙ I) : totalFold A.base ⟶ I :=
  let h : A.ε.addr = terminalCarrier A.base.n := funext fun x => Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (A.ε.addr x).isLt))
  eqToHom (congrArg (fun f => standardPushObj f A.base.val (0 : Fin 1)) h.symm) ≫
    A.ε.cell (0 : Fin 1) |> fun p =>
      eqToHom (congrArg (fold 𝒮 Zₐ A.base.val) (fibreList_terminal A.base.n 0).symm) ≫ p

set_option backward.isDefEq.respectTransparency false in
theorem totalAug_nativeCell {I : C} (A : Aug ℙ I) : totalAug A.base (totalNativeCell A) = A := by
  obtain ⟨a, ⟨f, c⟩⟩ := A
  have h : f = terminalCarrier a.n := funext fun x => Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (f x).isLt))
  subst f
  apply congrArg (fun e : Hom ℙ a (terminalShape I) => (⟨a, e⟩ : Aug ℙ I))
  apply native_hom_iff_cell rfl _ _ |>.2
  intro j
  have hj : j = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  change _ = 𝟙 _ ≫ c (0 : Fin 1)
  simp only [totalNativeCell, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, eqToHom_trans]
  simp

theorem totalAug_nativeCell_epsilon {I : C} (A : Aug ℙ I) :
    (totalAug A.base (totalNativeCell A)).ε = A.ε :=
  eq_of_heq (by
    have h (B D : Aug ℙ I) (e : B = D) : HEq B.ε D.ε := by cases e; rfl
    exact h _ _ (totalAug_nativeCell A))

variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (c : T.obj I I ⟶ I)

noncomputable def independentAug (A B : Aug ℙ I) : Aug ℙ I :=
  independentWordAug T R L A.base B.base (totalNativeCell A) (totalNativeCell B) c

variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

set_option backward.isDefEq.respectTransparency false in
noncomputable def independentAugMap {A B D E : Aug ℙ I}
    (p : AugHom ℙ A B) (q : AugHom ℙ D E) :
    AugHom ℙ (independentAug R L c A D) (independentAug R L c B E) :=
  independentNativeAugMap T R L N NR NL
    ⟨p.native, by rw [totalAug_nativeCell_epsilon, totalAug_nativeCell_epsilon]; exact p.preserves⟩
    ⟨q.native, by rw [totalAug_nativeCell_epsilon, totalAug_nativeCell_epsilon]; exact q.preserves⟩
    c (fun _ => hl _) (hr _) (hr _)

theorem independentAugMap_native {A B D E : Aug ℙ I}
    (p : AugHom ℙ A B) (q : AugHom ℙ D E) :
    (independentAugMap R L c N NR NL hl hr p q).native =
      independentNativeWordMap T p.native q.native R L := rfl

set_option backward.isDefEq.respectTransparency false in
theorem independentAugMap_ident (A B : Aug ℙ I) :
    independentAugMap R L c N NR NL hl hr (AugHom.ident A) (AugHom.ident B) =
      AugHom.ident (independentAug R L c A B) :=
  AugHom.ext (independentNativeWordMap_ident R L A.base B.base hl hr)

set_option backward.isDefEq.respectTransparency false in
theorem independentAugMap_comp {A B D E F G : Aug ℙ I}
    (p : AugHom ℙ A B) (q : AugHom ℙ D E)
    (p' : AugHom ℙ B F) (q' : AugHom ℙ E G) :
    independentAugMap R L c N NR NL hl hr (p.comp p') (q.comp q') =
      (independentAugMap R L c N NR NL hl hr p q).comp
        (independentAugMap R L c N NR NL hl hr p' q') :=
  AugHom.ext (independentNativeWordMap_comp R L N NR NL p.native q.native p'.native q'.native hl hr)

/-- Fixed right-associated ordered fold. Arity zero is the one-address
augmented unit, not the zero-address family. Arity one is exact. -/
noncomputable def independentAugFold :
    (n : Nat) → (Fin n → Aug ℙ I) → Aug ℙ I
  | 0, _ => AugHom.unit I
  | 1, A => A 0
  | n + 2, A => independentAug R L c (A 0)
      (independentAugFold (n + 1) (fun j => A j.succ))

noncomputable def independentAugFoldMap :
    (n : Nat) → {A B : Fin n → Aug ℙ I} →
      (∀ j, AugHom ℙ (A j) (B j)) →
      AugHom ℙ (independentAugFold R L c n A) (independentAugFold R L c n B)
  | 0, _, _, _ => AugHom.ident _
  | 1, _, _, p => p 0
  | n + 2, _, _, p => independentAugMap R L c N NR NL hl hr (p 0)
      (independentAugFoldMap (n + 1) (fun j => p j.succ))

theorem independentAugFoldMap_ident :
    (n : Nat) → (A : Fin n → Aug ℙ I) →
    independentAugFoldMap R L c N NR NL hl hr n (fun j => AugHom.ident (A j)) =
      AugHom.ident (independentAugFold R L c n A)
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, A => by
    simp only [independentAugFoldMap, independentAugFold,
      independentAugFoldMap_ident (n + 1) (fun j => A j.succ), independentAugMap_ident]

theorem independentAugFoldMap_comp :
    (n : Nat) → {A B D : Fin n → Aug ℙ I} →
    (p : ∀ j, AugHom ℙ (A j) (B j)) →
    (q : ∀ j, AugHom ℙ (B j) (D j)) →
    independentAugFoldMap R L c N NR NL hl hr n (fun j => (p j).comp (q j)) =
      (independentAugFoldMap R L c N NR NL hl hr n p).comp
        (independentAugFoldMap R L c N NR NL hl hr n q)
  | 0, _, _, _, _, _ => (AugHom.ident_comp _).symm
  | 1, _, _, _, _, _ => rfl
  | n + 2, _, _, _, p, q => by
    simp only [independentAugFoldMap,
      independentAugFoldMap_comp (n + 1) (fun j => p j.succ) (fun j => q j.succ),
      independentAugMap_comp]
    rfl

/-- The raw pair is read from the actual standard native product position.
Its inverse finds the position of that pair, not of the coefficient label. -/
noncomputable def independentPairEquiv (A B : Family C) :
    Fin (independentWord A B).length ≃ Fin A.n × Fin B.n where
  toFun i := (independentWord A B)[i]
  invFun := independentPairIndex A B
  left_inv i := by
    unfold independentPairIndex
    apply (wordPositions _ (independentWord_nodup A B)).injective
    rw [Equiv.apply_symm_apply]
    rfl
  right_inv := independentPairIndex_read A B

omit lF rF in
theorem independentPairEquiv_addr {A B D E : Family C}
    (p : Hom ℙ A B) (q : Hom ℙ D E)
    (i : Fin (independentWord A D).length) :
    independentPairEquiv B E ((independentNativeWordMap T p q R L).addr i) =
      Prod.map p.addr q.addr (independentPairEquiv A D i) := by
  exact wordCarrier_get _ (independent_word_support p q) _ i

/-- Read a native folded position as its ordered tuple of original axis
positions. This is an address reading, even when all labels coincide. -/
noncomputable def independentAugFoldRead :
    (n : Nat) → (A : Fin n → Aug ℙ I) →
    Fin (independentAugFold R L c n A).base.n → (∀ j, Fin (A j).base.n)
  | 0, _, _ => fun j => j.elim0
  | 1, _, k => Fin.cases k (fun j => j.elim0)
  | n + 2, A, k =>
    let w := independentPairEquiv (A 0).base
      (independentAugFold R L c (n + 1) (fun j => A j.succ)).base k
    Fin.cases w.1 (independentAugFoldRead (n + 1) (fun j => A j.succ) w.2)

theorem independentAugFoldRead_addr :
    (n : Nat) → {A B : Fin n → Aug ℙ I} →
    (p : ∀ j, AugHom ℙ (A j) (B j)) →
    (k : Fin (independentAugFold R L c n A).base.n) →
    independentAugFoldRead R L c n B ((independentAugFoldMap R L c N NR NL hl hr n p).native.addr k) =
      fun j => (p j).native.addr (independentAugFoldRead R L c n A k j)
  | 0, _, _, _, _ => funext fun j => j.elim0
  | 1, _, _, _, _ => by
    funext j
    have h : j = (0 : Fin 1) := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
    subst j
    rfl
  | n + 2, A, B, p, k => by
    let a := independentAugFold R L c (n + 1) (fun j => A j.succ)
    let b := independentAugFold R L c (n + 1) (fun j => B j.succ)
    let q := independentAugFoldMap R L c N NR NL hl hr (n + 1) (fun j => p j.succ)
    let w := independentPairEquiv (A 0).base a.base k
    have h := independentPairEquiv_addr R L (p 0).native q.native k
    have h' := independentAugFoldRead_addr (n + 1) (fun j => p j.succ) w.2
    simp only [independentAugFoldRead, independentAugFoldMap, independentAugMap_native]
    rw [h]
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cases_zero, Prod.map_fst]
    · simp only [Fin.cases_succ, Prod.map_snd]
      exact congrFun h' i

omit lF rF in
theorem independentAugFoldRead_bijective :
    (n : Nat) → (A : Fin n → Aug ℙ I) →
      Function.Bijective (independentAugFoldRead R L c n A)
  | 0, _ => by
    refine ⟨fun i j _ => Fin.ext ((Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)).trans
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)).symm), ?_⟩
    exact fun f => ⟨(0 : Fin 1), funext fun j => j.elim0⟩
  | 1, A => by
    refine ⟨fun i j h => ?_, fun f => ⟨f 0, ?_⟩⟩
    · have e := congrFun h 0
      exact e
    · funext j
      refine Fin.cases ?_ (fun i => i.elim0) j
      simp only [independentAugFoldRead, Fin.cases_zero]
  | n + 2, A => by
    let a := independentAugFold R L c (n + 1) (fun j => A j.succ)
    let e := independentPairEquiv (A 0).base a.base
    let r := independentAugFoldRead R L c (n + 1) (fun j => A j.succ)
    have h := independentAugFoldRead_bijective (n + 1) (fun j => A j.succ)
    constructor
    · intro i j eq
      apply e.injective
      apply Prod.ext
      · have p := congrFun eq 0
        simpa only [independentAugFoldRead, Fin.cases_zero] using p
      · apply h.1
        funext k
        have p := congrFun eq k.succ
        simpa only [independentAugFoldRead, Fin.cases_succ] using p
    · intro f
      obtain ⟨k, g⟩ := h.2 (fun j => f j.succ)
      refine ⟨e.symm (f 0,k), ?_⟩
      funext j
      change Fin.cases (e (e.symm (f 0,k))).1 (r (e (e.symm (f 0,k))).2) j = f j
      rw [Equiv.apply_symm_apply]
      refine Fin.cases ?_ (fun z => ?_) j
      · simp only [Fin.cases_zero]
      · simp only [Fin.cases_succ]
        exact congrFun g z

noncomputable def independentAugFoldPositions (n : Nat) (A : Fin n → Aug ℙ I) :
    Fin (independentAugFold R L c n A).base.n ≃ (∀ j, Fin (A j).base.n) :=
  Equiv.ofBijective _ (independentAugFoldRead_bijective R L c n A)

/-- A native folded fibre is the entire coordinatewise inverse image.
An unhit axis makes this fibre empty, but the native cell still exists. -/
theorem independentAugFold_fibre_iff (n : Nat) {A B : Fin n → Aug ℙ I}
    (p : ∀ j, AugHom ℙ (A j) (B j))
    (i : Fin (independentAugFold R L c n A).base.n)
    (k : Fin (independentAugFold R L c n B).base.n) :
    i ∈ fibreList (independentAugFoldMap R L c N NR NL hl hr n p).native.addr k ↔
      ∀ j, (p j).native.addr (independentAugFoldRead R L c n A i j) =
        independentAugFoldRead R L c n B k j := by
  rw [mem_fibreList, ← (independentAugFoldRead_bijective R L c n B).1.eq_iff,
    independentAugFoldRead_addr]
  exact ⟨fun e j => congrFun e j, fun e => funext e⟩

/-- Coefficient nesting independently described on the original coordinate list. -/
def independentAugCoefficient (T : Bi (coeff (C:=C))) (I : C) :
    (n : Nat) → (Fin n → C) → C
  | 0, _ => I
  | 1, A => A 0
  | n + 2, A => T.obj (A 0) (independentAugCoefficient T I (n + 1) (fun j => A j.succ))

omit lF rF in
theorem independentAugFold_label :
    (n : Nat) → (A : Fin n → Aug ℙ I) →
    (k : Fin (independentAugFold R L c n A).base.n) →
    (independentAugFold R L c n A).base.val k =
      independentAugCoefficient T I n
        (fun j => (A j).base.val (independentAugFoldRead R L c n A k j))
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | n + 2, A, k => by
    let a := independentAugFold R L c (n + 1) (fun j => A j.succ)
    let w := independentPairEquiv (A 0).base a.base k
    have h := independentAugFold_label (n + 1) (fun j => A j.succ) w.2
    change T.obj ((A 0).base.val w.1) (a.base.val w.2) = _
    simp only [independentAugCoefficient, independentAugFoldRead, Fin.cases_zero, Fin.cases_succ]
    exact congrArg (T.obj ((A 0).base.val w.1)) h

omit lF rF in
theorem independentAugFold_zero_positions (A : Fin 0 → Aug ℙ I) :
    (independentAugFold R L c 0 A).base.n = 1 := rfl

/-- A missing local axis fibre forces a genuinely empty joint fibre, not
an identification of its opaque target cell with some canonical zero map. -/
theorem independentAugFold_empty_axis (n : Nat) {A B : Fin n → Aug ℙ I}
    (p : ∀ j, AugHom ℙ (A j) (B j))
    (k : Fin (independentAugFold R L c n B).base.n) (j : Fin n)
    (h : ∀ i, (p j).native.addr i ≠ independentAugFoldRead R L c n B k j) :
    fibreList (independentAugFoldMap R L c N NR NL hl hr n p).native.addr k = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  exact h _ ((independentAugFold_fibre_iff R L c N NR NL hl hr n p i k).mp hi j)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
