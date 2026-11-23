module
public import ContextualComposition.NativeRawSingletonTrace
public import ContextualComposition.NativeIndependentWordArrow
@[expose] public section

/-! The native independent product preserves structural singleton
fibres. The result is about the original product arrow, not a newly
selected structural lift with the same underlying carrier. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w z
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

noncomputable def independentPosition (T : Bi (coeff (C:=C))) (A B : Family C) :
    Fin (independentFamily T A B).n ≃ (Fin A.n × Fin B.n) where
  toFun j := (independentWord A B)[j]
  invFun := independentPairIndex A B
  left_inv j := by
    apply Fin.ext
    exact (independentWord_nodup A B).getElem_inj.mp (independentPairIndex_read A B _)
  right_inv := independentPairIndex_read A B

set_option backward.isDefEq.respectTransparency false in
theorem independent_one_pair_cells {X Y : Type w} (A : X → C) (B : Y → C) (x : X) (y : Y)
    [(leftFactor T (A x)).LaxBraided] [(rightFactor (T:=T) (B y)).LaxBraided]
    (hl : SameLeftGather T (A x) L) (hr : SameRightGather R (B y))
    {a b : C} (p : A x ⟶ a) (q : B y ⟶ b) :
    rectWordChart (fun z : X × Y => T.obj (A z.1) (B z.2)) [x] [y] ≫ independentCell R L A B [x] [y]
      ((ρ_ (A x)).hom ≫ p) ((ρ_ (B y)).hom ≫ q) =
      (ρ_ (T.obj (A x) (B y))).hom ≫ T.map p q := by
  have h : T.map ((ρ_ (A x)).hom ≫ p) ((ρ_ (B y)).hom ≫ q) =
      T.map (ρ_ (A x)).hom (ρ_ (B y)).hom ≫ T.map p q :=
    (bi_map_comp (T:=T) (ρ_ (A x)).hom p (ρ_ (B y)).hom q).symm
  let r := rectWordChart (fun z : X × Y => T.obj (A z.1) (B z.2)) [x] [y]
  let g : (T.obj (A x) (B y) ⊗ Zₐ) ⊗ Zₐ ⟶ T.obj (A x ⊗ Zₐ) (B y ⊗ Zₐ) :=
    rowGather R L A B [x] [y]
  have k : r ≫ g ≫ T.map (ρ_ (A x)).hom (ρ_ (B y)).hom = (ρ_ (T.obj (A x) (B y))).hom :=
    independent_one_pair_unit R L A B x y hl hr
  change r ≫ (g ≫ T.map ((ρ_ (A x)).hom ≫ p) ((ρ_ (B y)).hom ≫ q)) = _
  rw [h, reassoc_of% k]

set_option backward.isDefEq.respectTransparency false in
theorem independentSingletonWordCell
    {A B A' B' : Family C} (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n)
    (p : ∀ j, A.val (e.symm j) ⟶ A'.val j) (q : ∀ j, B.val (d.symm j) ⟶ B'.val j)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
    (t : Fin A'.n × Fin B'.n) :
    HEq (independentWordCell T (nativeSingletonMap e p) (nativeSingletonMap d q) R L t)
      ((ρ_ (T.obj (A.val (e.symm t.1)) (B.val (d.symm t.2)))).hom ≫ T.map (p t.1) (q t.2)) := by
  let j := e.symm t.1
  let k := d.symm t.2
  let V := A.val
  let W := B.val
  let s := nativeSingletonMap e p
  let u := nativeSingletonMap d q
  let xs := fibreList e t.1
  let ys := fibreList d t.2
  let α := (ρ_ (V j)).hom ≫ p t.1
  let β := (ρ_ (W k)).hom ≫ q t.2
  have x : xs.map id = [j] := (List.map_id xs).trans (equiv_fibreList e t.1)
  have y : ys.map id = [k] := (List.map_id ys).trans (equiv_fibreList d t.2)
  have h := rectangleCell_map_heq' R L V W id id xs ys x y
    (nativeSingletonMap_cell_heq e p t.1) (nativeSingletonMap_cell_heq d q t.2)
  let _ := lF (V j)
  let _ := rF (W k)
  have nn := independent_one_pair_cells R L V W j k (hl _) (hr _) (p t.1) (q t.2)
  change HEq (eqToHom _ ≫ (rectWordChart (fun z => T.obj (V z.1) (W z.2)) xs ys ≫
    rowGather R L V W xs ys ≫ T.map (s.cell t.1) (u.cell t.2))) _
  have nn' : rectWordChart (fun z => T.obj (V z.1) (W z.2)) [j] [k] ≫ rowGather R L V W [j] [k] ≫ T.map α β =
      (ρ_ (T.obj (V j) (W k))).hom ≫ T.map (p t.1) (q t.2) := by
    exact nn
  exact (hom_source_pin_heq _ _).trans (h.trans (heq_of_eq nn'))


noncomputable def independentSingletonEquiv {A B A' B' : Family C}
    (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n) :
    Fin (independentFamily T A B).n ≃ Fin (independentFamily T A' B').n :=
  (independentPosition T A B).trans ((e.prodCongr d).trans (independentPosition T A' B').symm)

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem independentSingletonEquiv_read {A B A' B' : Family C}
    (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n) (j : Fin (independentFamily T A B).n) :
    independentPosition T A' B' (independentSingletonEquiv (T:=T) e d j) =
      Prod.map e d (independentPosition T A B j) := by
  unfold independentSingletonEquiv
  simp

omit [MonoidalCategory C] [SymmetricCategory C] in
theorem independentSingletonEquiv_read_symm {A B A' B' : Family C}
    (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n) (j : Fin (independentFamily T A' B').n) :
    independentPosition T A B ((independentSingletonEquiv (T:=T) e d).symm j) =
      Prod.map e.symm d.symm (independentPosition T A' B' j) := by
  unfold independentSingletonEquiv
  simp

noncomputable def independentSingletonCells {A B A' B' : Family C}
    (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n)
    (p : ∀ j, A.val (e.symm j) ⟶ A'.val j) (q : ∀ j, B.val (d.symm j) ⟶ B'.val j)
    (j : Fin (independentFamily T A' B').n) :
    (independentFamily T A B).val ((independentSingletonEquiv (T:=T) e d).symm j) ⟶
      (independentFamily T A' B').val j :=
  let t := independentPosition T A' B' j
  eqToHom (congrArg (independentLabels T A B) (independentSingletonEquiv_read_symm e d j)) ≫
    T.map (p t.1) (q t.2)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
theorem independentNativeSingletonMap {A B A' B' : Family C}
    (e : Fin A.n ≃ Fin A'.n) (d : Fin B.n ≃ Fin B'.n)
    (p : ∀ j, A.val (e.symm j) ⟶ A'.val j) (q : ∀ j, B.val (d.symm j) ⟶ B'.val j)
    [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b) :
    independentNativeWordMap T (nativeSingletonMap e p) (nativeSingletonMap d q) R L =
      nativeSingletonMap (independentSingletonEquiv (T:=T) e d) (independentSingletonCells (T:=T) e d p q) := by
  let F := independentFamily T A B
  let G := independentFamily T A' B'
  let E := independentSingletonEquiv (T:=T) e d
  let c := independentSingletonCells (T:=T) e d p q
  let m := nativeSingletonMap e p
  let n := nativeSingletonMap d q
  let x := independentNativeWordMap T m n R L
  let y := nativeSingletonMap E c
  change x = y
  apply native_hom_eq_of_cell_heq
  · funext i
    apply (independentPosition T A' B').injective
    have h := wordCarrier_get (Prod.map m.addr n.addr) (independent_word_support m n) (independentWord_nodup A' B') i
    exact h.trans (independentSingletonEquiv_read (T:=T) e d i).symm
  · intro j
    let t := independentPosition T A' B' j
    let ζ := T.obj (A.val (e.symm t.1)) (B.val (d.symm t.2))
    let h : F.val (E.symm j) = ζ :=
      congrArg (independentLabels T A B) (independentSingletonEquiv_read_symm (T:=T) e d j)
    let r := T.map (p t.1) (q t.2)
    have Hx : HEq (x.cell j) ((ρ_ ζ).hom ≫ r) :=
      (hom_source_pin_heq _ _).trans (independentSingletonWordCell R L e d p q hl hr t)
    have Hy : HEq (y.cell j) ((ρ_ (F.val (E.symm j))).hom ≫ c j) :=
      nativeSingletonMap_cell_heq E c j
    have Hc : HEq (c j) r := hom_source_pin_heq h r
    have Hρ {s t : C} (w : s = t) : HEq (ρ_ s).hom (ρ_ t).hom := by subst t; rfl
    exact Hx.trans ((Hy.trans (structural_seq_heq (K:=coeff (C:=C))
      (congrArg (fun o => o ⊗ Zₐ) h) h rfl (Hρ h) Hc)).symm)


noncomputable def RawSingletonFrame.tensor {Ω : Type w} {Θ : Type z} {A B : Family C}
    (T : Bi (coeff (C:=C))) (F : RawSingletonFrame Ω A) (G : RawSingletonFrame Θ B) :
    RawSingletonFrame (Ω × Θ) (independentFamily T A B) where
  read j := Prod.map F.read G.read (independentPosition T A B j)
  label z := T.obj (F.label z.1) (G.label z.2)
  at_read j := congrArg₂ T.obj (F.at_read (independentPosition T A B j).1) (G.at_read (independentPosition T A B j).2)
  injective := by
    intro i j h
    apply (independentPosition T A B).injective
    exact Prod.ext (F.injective (congrArg Prod.fst h)) (G.injective (congrArg Prod.snd h))

set_option backward.isDefEq.respectTransparency false in
theorem RawSingletonTrace.tensor {Ω : Type w} {Θ : Type z} {A B A' B' : Family C}
    {F : RawSingletonFrame Ω A} {F' : RawSingletonFrame Ω A'}
    {G : RawSingletonFrame Θ B} {G' : RawSingletonFrame Θ B'}
    {a : ∀ i, F.label i ⟶ F'.label i} {b : ∀ i, G.label i ⟶ G'.label i}
    {f : Hom ℙ A A'} {g : Hom ℙ B B'}
    [lF : ∀ t : C, (leftFactor T t).LaxBraided] [rF : ∀ t : C, (rightFactor (T:=T) t).LaxBraided]
    (hl : ∀ t : C, SameLeftGather T t L) (hr : ∀ t : C, SameRightGather R t)
    (hf : RawSingletonTrace F F' a f) (hg : RawSingletonTrace G G' b g) :
    RawSingletonTrace (F.tensor T G) (F'.tensor T G')
      (fun z => T.map (a z.1) (b z.2)) (independentNativeWordMap T f g R L) := by
  obtain ⟨e,p,rfl,he,hp⟩ := hf
  obtain ⟨d,q,rfl,hd,hq⟩ := hg
  refine ⟨independentSingletonEquiv (T:=T) e d, independentSingletonCells (T:=T) e d p q,
    independentNativeSingletonMap R L e d p q hl hr, ?_, ?_⟩
  · intro i
    change Prod.map F'.read G'.read (independentPosition T A' B' (independentSingletonEquiv (T:=T) e d i)) =
      Prod.map F.read G.read (independentPosition T A B i)
    rw [independentSingletonEquiv_read]
    exact Prod.ext (he _) (hd _)
  · intro j
    let v := independentPosition T A' B' j
    have h₀ := (F.at_read (e.symm v.1)).trans
      (congrArg F.label (RawSingletonTrace.symm_read e he v.1))
    have h₁ := (G.at_read (d.symm v.2)).trans
      (congrArg G.label (RawSingletonTrace.symm_read d hd v.2))
    exact (hom_source_pin_heq _ _).trans
      (structural_map_heq (S:=T) h₀ (F'.at_read v.1) h₁ (G'.at_read v.2) (hp v.1) (hq v.2))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
