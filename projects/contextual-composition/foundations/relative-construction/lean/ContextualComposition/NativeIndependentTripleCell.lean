module
public import ContextualComposition.NativeIndependentTripleChart
public import ContextualComposition.NativeDependentLeftUnitNaturality
@[expose] public section

/-! Three arbitrary whole source cells across a regrouping of the native
independent product. Empty source axis fibres are not replaced by units. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {X Y W : Type u} (A : X → C) (B : Y → C) (D : W → C)
variable (xs : List X) (ys : List Y) (ws : List W)
local notation "a" => fold 𝒮 Zₐ A xs
local notation "b" => fold 𝒮 Zₐ B ys
local notation "d" => fold 𝒮 Zₐ D ws
variable {a' b' d' : C}
variable (p : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ a')
variable (q : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ b')
variable (r : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D ws ⟶ d')

def tripleIndependentLeftCell :=
  let V := crossLabel T A B
  let x := rectWordChart V xs ys ≫ independentCell R L A B xs ys p q
  rectWordChart (crossLabel T V D) (xs.product ys) ws ≫ independentCell R L V D (xs.product ys) ws x r

def tripleIndependentRightCell :=
  let V := crossLabel T B D
  let x := rectWordChart V ys ws ≫ independentCell R L B D ys ws q r
  rectWordChart (crossLabel T A V) xs (ys.product ws) ≫ independentCell R L A V xs (ys.product ws) p x

set_option backward.isDefEq.respectTransparency false in
theorem tripleIndependentLeftCell_flat :
    tripleIndependentLeftCell R L A B D xs ys ws p q r =
      tripleLeftFlatGather R L A B D xs ys ws ≫ T.map (T.map p q) r := by
  let V := crossLabel T A B
  let h := rectWordChart V xs ys ≫ rowGather R L A B xs ys
  have k : T.map (h ≫ T.map p q) r = T.map h (𝟙 d) ≫ T.map (T.map p q) r := by
    rw [bi_map_comp, Category.id_comp]
  unfold tripleIndependentLeftCell tripleLeftFlatGather independentCell
  simp only [Category.assoc]
  have k' : T.map (rectWordChart V xs ys ≫ rowGather R L A B xs ys ≫ T.map p q) r =
      T.map h (𝟙 d) ≫ T.map (T.map p q) r := by
    rw [← Category.assoc]
    exact k
  rw [k']

set_option backward.isDefEq.respectTransparency false in
theorem tripleIndependentRightCell_flat :
    tripleIndependentRightCell R L A B D xs ys ws p q r =
      tripleRightFlatGather R L A B D xs ys ws ≫ T.map p (T.map q r) := by
  let V := crossLabel T B D
  let h := rectWordChart V ys ws ≫ rowGather R L B D ys ws
  have k : T.map p (h ≫ T.map q r) = T.map (𝟙 a) h ≫ T.map p (T.map q r) := by
    rw [bi_map_comp, Category.id_comp]
  unfold tripleIndependentRightCell tripleRightFlatGather independentCell
  simp only [Category.assoc]
  have k' : T.map p (rectWordChart V ys ws ≫ rowGather R L B D ys ws ≫ T.map q r) =
      T.map (𝟙 a) h ≫ T.map p (T.map q r) := by
    rw [← Category.assoc]
    exact k
  rw [k']

set_option backward.isDefEq.respectTransparency false in
include NR NL in
theorem tripleIndependentCell_assoc (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P)
    [lF : ∀ c : C, (leftFactor T c).LaxBraided] (hl : ∀ c : C, SameLeftGather T c L)
    [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided] (hr : ∀ c : C, SameRightGather R c) :
    HEq (tripleIndependentLeftCell R L A B D xs ys ws p q r ≫ P.assoc a' b' d')
      (act 𝒮 Zₐ (fun z : X × Y × W => P.assoc (A z.1) (B z.2.1) (D z.2.2)) (xs.product (ys.product ws)) ≫
        tripleIndependentRightCell R L A B D xs ys ws p q r) := by
  let H := crossLabel T (crossLabel T A B) D
  let H' := H ∘ (tripleRetag (X:=X) (Y:=Y) (W:=W)).symm
  let v := (xs.product ys).product ws
  let w := xs.product (ys.product ws)
  let e := (std_fold_map H' tripleRetag v).symm.trans
    (congrArg (fold 𝒮 Zₐ H') (tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)))
  let s := tripleLeftFlatGather R L A B D xs ys ws
  let t := tripleRightFlatGather R L A B D xs ys ws
  let A₀ := act 𝒮 Zₐ (fun z : X × Y × W => P.assoc (A z.1) (B z.2.1) (D z.2.2)) w
  have h := tripleFlatGather_assoc R L NR NL A B D xs ys ws P Q hl hr
  have hn : T.map (T.map p q) r ≫ P.assoc a' b' d' =
    P.assoc a b d ≫ T.map p (T.map q r) := P.assoc_nat p q r
  rw [tripleIndependentLeftCell_flat, tripleIndependentRightCell_flat]
  change HEq ((s ≫ T.map (T.map p q) r) ≫ P.assoc a' b' d') (A₀ ≫ t ≫ T.map p (T.map q r))
  rw [Category.assoc, hn, ← Category.assoc s, ← Category.assoc A₀]
  exact structural_seq_heq (K:=coeff (C:=C)) e rfl rfl h HEq.rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
