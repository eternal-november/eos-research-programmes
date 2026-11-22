module
public import ContextualComposition.NativeWordTerminal
@[expose] public section

/-! Exact native independent augmentation criterion with the literal
product arrow and the literal terminal charts. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C

omit [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] in
theorem independentWord_nodup (A B : Family C) : (independentWord A B).Nodup :=
  nodup_product_word (List.nodup_finRange _) (List.nodup_finRange _)

def independentWordAugCell (T : Bi (coeff (C:=C))) (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (A B : Family C) {I : C} (δ : totalFold A ⟶ I) (η : totalFold B ⟶ I) (c : T.obj I I ⟶ I) :
    fold 𝒮 Zₐ (independentLabels T A B) (independentWord A B) ⟶ I :=
  rectWordChart (independentLabels T A B) (List.finRange A.n) (List.finRange B.n) ≫
    rowGather R L A.val B.val (List.finRange A.n) (List.finRange B.n) ≫ T.map δ η ≫ c

noncomputable def independentWordAug (T : Bi (coeff (C:=C))) (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (A B : Family C) {I : C} (δ : totalFold A ⟶ I) (η : totalFold B ⟶ I) (c : T.obj I I ⟶ I) :
    Aug ℙ I :=
  wordAug (independentLabels T A B) (independentWord A B) (independentWordAugCell T R L A B δ η c)

set_option backward.isDefEq.respectTransparency false in
theorem independentNativeWordMap_aug_iff (T : Bi (coeff (C:=C))) (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {A B A' B' : Family C} {I : C}
    (p : Hom ℙ A A') (q : Hom ℙ B B')
    (δ : totalFold A ⟶ I) (η : totalFold B ⟶ I) (δ' : totalFold A' ⟶ I) (η' : totalFold B' ⟶ I)
    (c : T.obj I I ⟶ I) :
    let xys := independentWord A B
    let uvs := independentWord A' B'
    let A₀ := independentLabels T A B
    let A₁ := independentLabels T A' B'
    let F := Prod.map p.addr q.addr
    let h := independent_word_support p q
    let j := fun i : Fin uvs.length => independentWordCell T p q R L uvs[i]
    let α := independentWordAugCell T R L A B δ η c
    let β := independentWordAugCell T R L A' B' δ' η' c
    let rr := wordNativePartitionOrder F h (independentWord_nodup A' B')
    (independentNativeWordMap T p q R L).comp (independentWordAug T R L A' B' δ' η' c).ε =
      (independentWordAug T R L A B δ η c).ε ↔
    AddressOrder.mapSum additiveStructure A₀ rr ≫
      rowsChart A₀ (fun i => wordFibre xys F uvs[i]) (List.finRange uvs.length) ≫
      act 𝒮 Zₐ j (List.finRange uvs.length) ≫ eqToHom (wordTotalPin A₁ uvs) ≫ β = α := by
  intro xys uvs A₀ A₁ F h j α β rr
  exact wordNativeMap_preserving_iff F h (independentWord_nodup A B)
    (independentWord_nodup A' B') A₀ A₁ j rr α β

private theorem rect_target_gather_nat {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {X Y : Type} {A B : X → C} {D E : Y → C} (xs : List X) (ys : List Y)
    (p : ∀ x, A x ⟶ B x) (q : ∀ y, D y ⟶ E y) :
    (coeff (C:=C)).seq (act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => T.map (p x) (q y)) ys) xs)
      (rowGather R L B E xs ys) =
    (coeff (C:=C)).seq (rowGather R L A D xs ys)
      (T.map (act 𝒮 Zₐ p xs) (act 𝒮 Zₐ q ys)) := by
  let K := coeff (C:=C)
  have side (x : X) :
      K.seq (act 𝒮 Zₐ (fun y => T.map (p x) (q y)) ys) ((Lin.left L (B x)).collect E ys) =
        K.seq ((Lin.left L (A x)).collect D ys) (T.map (p x) (act 𝒮 Zₐ q ys)) := by
    have e : (fun y => T.map (p x) (q y)) =
        fun y => K.seq (T.map (p x) (K.id (D y))) (T.map (K.id (B x)) (q y)) := by
      funext y
      rw [← T.map_seq, K.seq_id, K.id_seq]
    rw [e, ← act_seq, K.assoc, Lin.collect_nat _ (NL.inner (B x)), ← K.assoc]
    rw [← (NL.outer (p x)).collect D ys, K.assoc, ← T.map_seq, K.seq_id, K.id_seq]
  unfold rowGather tally
  rw [← K.assoc, act_seq]
  simp only [side]
  rw [← act_seq, K.assoc]
  have e : (fun x => T.map (p x) (act 𝒮 Zₐ q ys)) =
      fun x => K.seq (T.map (K.id (A x)) (act 𝒮 Zₐ q ys))
        (T.map (p x) (K.id (fold 𝒮 Zₐ E ys))) := by
    funext x
    rw [← T.map_seq, K.id_seq, K.seq_id]
  rw [e, ← act_seq, K.assoc, gather_outer NR]
  rw [← K.assoc (act 𝒮 Zₐ (fun x => T.map (K.id (A x)) (act 𝒮 Zₐ q ys)) xs), ← gather_nat, K.assoc,
    ← T.map_seq, K.id_seq, K.seq_id]
  exact (K.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- After the literal independent fibre cells, push the two opaque axis
maps through the target rectangle's specified chart and gather.  Only
their source-side structural regrouping remains. -/
theorem independent_native_terminal_cells (T : Bi (coeff (C:=C)))
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {A B A' B' : Family C} (p : Hom ℙ A A') (q : Hom ℙ B B') :
    let xs := List.finRange A'.n
    let ys := List.finRange B'.n
    let A₀ := independentLabels T A B
    let A₁ := independentLabels T A' B'
    let X := standardPushObj p.addr A.val
    let Y := standardPushObj q.addr B.val
    let H := fun (t : Fin A'.n × Fin B'.n) => T.obj (X t.1) (Y t.2)
    let ψ := fun (t : Fin A'.n × Fin B'.n) =>
      (eqToHom (congrArg (fold 𝒮 Zₐ A₀) (independent_get_fibre p q t)) ≫
      rectWordChart A₀ (fibreList p.addr t.1) (fibreList q.addr t.2)) ≫
      rowGather R L A.val B.val (fibreList p.addr t.1) (fibreList q.addr t.2)
    act 𝒮 Zₐ (independentWordCell T p q R L) (xs.product ys) ≫
      rectWordChart A₁ xs ys ≫ rowGather R L A'.val B'.val xs ys =
    act 𝒮 Zₐ ψ (xs.product ys) ≫ rectWordChart H xs ys ≫
      rowGather R L X Y xs ys ≫ T.map (act 𝒮 Zₐ p.cell xs) (act 𝒮 Zₐ q.cell ys) := by
  intro xs ys A₀ A₁ X Y H ψ
  let τ : (t : Fin A'.n × Fin B'.n) → H t ⟶ A₁ t := fun t => T.map (p.cell t.1) (q.cell t.2)
  let f := fun t => independentWordCell T p q R L t
  let w := xs.product ys
  have h (t : Fin A'.n × Fin B'.n) : f t = ψ t ≫ τ t := by
    unfold f independentWordCell independentCell ψ τ
    simp only [Category.assoc]
    rfl
  have h' : act 𝒮 Zₐ f w = act 𝒮 Zₐ ψ w ≫ act 𝒮 Zₐ τ w :=
    (congrArg (fun g => act 𝒮 Zₐ g w) (funext h)).trans (act_seq 𝒮 Zₐ ψ τ w).symm
  have h₀ := rectWordChart_natural τ xs ys
  have h₁ := rect_target_gather_nat R L NR NL xs ys p.cell q.cell
  change act 𝒮 Zₐ f w ≫ rectWordChart A₁ xs ys ≫ rowGather R L A'.val B'.val xs ys = _
  rw [h']
  simp only [Category.assoc]
  have h₂ : act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun y => τ (x,y)) ys) xs ≫
      rowGather R L A'.val B'.val xs ys =
      rowGather R L X Y xs ys ≫ T.map (act 𝒮 Zₐ p.cell xs) (act 𝒮 Zₐ q.cell ys) := h₁
  have h₃ := congrArg (fun k => act 𝒮 Zₐ ψ w ≫ k ≫ rowGather R L A'.val B'.val xs ys) h₀
  simp only [Category.assoc] at h₃
  exact h₃.trans (congrArg (fun k => act 𝒮 Zₐ ψ w ≫ rectWordChart H xs ys ≫ k) h₂)

set_option backward.isDefEq.respectTransparency false in
/-- Exact remaining source structural equation. Its inputs are carrier
functions and coefficient labels, never the input opaque aggregation
arrows or either augmentation. -/
def IndependentProductSourceChart (T : Bi (coeff (C:=C)))
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    {A B : Family C} {n m : Nat} (f : Fin A.n → Fin n) (g : Fin B.n → Fin m)
    (r : AddressOrder (Fin A.n × Fin B.n) (independentWord A B)
      (((List.finRange n).product (List.finRange m)).flatMap (wordFibre (independentWord A B) (Prod.map f g)))) : Prop :=
  let xs := List.finRange n
  let ys := List.finRange m
  let H₀ := independentLabels T A B
  let X := standardPushObj f A.val
  let Y := standardPushObj g B.val
  let H := fun (t : Fin n × Fin m) => T.obj (X t.1) (Y t.2)
  let F := Prod.map f g
  let d := fun (t : Fin n × Fin m) =>
    (product_word_fibre (List.finRange A.n) (List.finRange B.n) f g t).trans
      (by simp only [wordFibre, fibreList, beq_eq_decide])
  let ψ := fun (t : Fin n × Fin m) =>
    (eqToHom (congrArg (fold 𝒮 Zₐ H₀) (d t)) ≫
      rectWordChart H₀ (fibreList f t.1) (fibreList g t.2)) ≫
      rowGather R L A.val B.val (fibreList f t.1) (fibreList g t.2)
  AddressOrder.mapSum additiveStructure H₀ r ≫ rowsChart H₀ (wordFibre (independentWord A B) F) (xs.product ys) ≫
      act 𝒮 Zₐ ψ (xs.product ys) ≫ rectWordChart H xs ys ≫ rowGather R L X Y xs ys =
    rectWordChart H₀ (List.finRange A.n) (List.finRange B.n) ≫
      rowGather R L A.val B.val (List.finRange A.n) (List.finRange B.n) ≫
      T.map (AddressOrder.mapSum additiveStructure A.val (totalPartitionOrder f) ≫ rowsChart A.val (fibreList f) xs)
        (AddressOrder.mapSum additiveStructure B.val (totalPartitionOrder g) ≫ rowsChart B.val (fibreList g) ys)

set_option backward.isDefEq.respectTransparency false in
/-- From the purely structural source-chart identity, build the actual
native product AugHom with exactly the independent opaque cells. -/
noncomputable def independentNativeAugMap_of_sourceChart (T : Bi (coeff (C:=C)))
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ)
    (NR : GatherOuterNat R) (NL : GatherLeftNat L)
    {A B A' B' : Family C} {I : C}
    {δ : totalFold A ⟶ I} {η : totalFold B ⟶ I} {δ' : totalFold A' ⟶ I} {η' : totalFold B' ⟶ I}
    (p : AugHom ℙ (totalAug A δ) (totalAug A' δ'))
    (q : AugHom ℙ (totalAug B η) (totalAug B' η'))
    (c : T.obj I I ⟶ I)
    (r : AddressOrder (Fin A.n × Fin B.n) (independentWord A B)
      ((independentWord A' B').flatMap (wordFibre (independentWord A B) (Prod.map p.native.addr q.native.addr))))
    (S : IndependentProductSourceChart T R L (A:=A) (B:=B) p.native.addr q.native.addr r) :
    AugHom ℙ (independentWordAug T R L A B δ η c) (independentWordAug T R L A' B' δ' η' c) where
  native := independentNativeWordMap T p.native q.native R L
  preserves := by
    let p₀ : Hom ℙ A A' := p.native
    let q₀ : Hom ℙ B B' := q.native
    let H₀ := independentLabels T A B
    let H₁ := independentLabels T A' B'
    let xs := List.finRange A'.n
    let ys := List.finRange B'.n
    let xy := List.finRange A.n
    let yy := List.finRange B.n
    let w := xs.product ys
    let v := xy.product yy
    let F := Prod.map p₀.addr q₀.addr
    let p' := independentWordCell T p₀ q₀ R L
    let α := independentWordAugCell T R L A B δ η c
    let β := independentWordAugCell T R L A' B' δ' η' c
    change (wordNativeMap F (independent_word_support p₀ q₀) (independentWord_nodup A' B') H₀ H₁ (fun i => p' w[i])).comp
      (wordAug H₁ w β).ε = (wordAug H₀ v α).ε
    apply (wordNativeMap_raw_preserving_iff F (independent_word_support p₀ q₀)
      (independentWord_nodup A B) (independentWord_nodup A' B') H₀ H₁ p' r α β).mpr
    let a := AddressOrder.mapSum additiveStructure H₀ r
    let b := rowsChart H₀ (wordFibre v F) w
    let D := act 𝒮 Zₐ p₀.cell xs
    let E := act 𝒮 Zₐ q₀.cell ys
    let a₀ := AddressOrder.mapSum additiveStructure A.val (totalPartitionOrder p₀.addr) ≫
      rowsChart A.val (fibreList p₀.addr) xs
    let b₀ := AddressOrder.mapSum additiveStructure B.val (totalPartitionOrder q₀.addr) ≫
      rowsChart B.val (fibreList q₀.addr) ys
    let V := rectWordChart H₀ xy yy ≫ rowGather R L A.val B.val xy yy
    have h := independent_native_terminal_cells T R L NR NL p₀ q₀
    let ω := T.map δ' η' ≫ c
    have h' := congrArg (fun z => a ≫ b ≫ z ≫ ω) h
    unfold IndependentProductSourceChart at S
    dsimp only at S h'
    simp only [Category.assoc] at S h'
    change a ≫ b ≫ act 𝒮 Zₐ p' w ≫
      (rectWordChart H₁ xs ys ≫ rowGather R L A'.val B'.val xs ys ≫ ω) = _
    refine h'.trans ?_
    have H := congrArg (fun z => z ≫ T.map D E ≫ ω) S
    simp only [Category.assoc] at H
    refine H.trans ?_
    have ep : a₀ ≫ D ≫ δ' = δ := by
      have h : wholeContinuation p₀ ≫ δ' = δ := wholeContinuation_preserves p
      simpa only [wholeContinuation, a₀, Category.assoc] using h
    have eq : b₀ ≫ E ≫ η' = η := by
      have h : wholeContinuation q₀ ≫ η' = η := wholeContinuation_preserves q
      simpa only [wholeContinuation, b₀, Category.assoc] using h
    have m : T.map a₀ b₀ ≫ T.map D E ≫ T.map δ' η' = T.map δ η := by
      change (coeff (C:=C)).seq (T.map a₀ b₀) ((coeff (C:=C)).seq (T.map D E) (T.map δ' η')) = _
      rw [← T.map_seq, ← T.map_seq]
      change T.map (a₀ ≫ D ≫ δ') (b₀ ≫ E ≫ η') = _
      rw [ep, eq]
    have n := congrArg (fun k => V ≫ k ≫ c) m
    change rectWordChart H₀ xy yy ≫ rowGather R L A.val B.val xy yy ≫
      T.map a₀ b₀ ≫ T.map D E ≫ T.map δ' η' ≫ c =
      rectWordChart H₀ xy yy ≫ rowGather R L A.val B.val xy yy ≫ T.map δ η ≫ c
    simpa only [V, Category.assoc] using n

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
