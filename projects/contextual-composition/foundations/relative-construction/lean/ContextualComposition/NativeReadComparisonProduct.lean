module
public import ContextualComposition.NativeFubiniTreeTrace
@[expose] public section

/-! Product of two structural comparisons, computed on the original
independent augmented arrow, and on literal parent/child inputs. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

section Word
variable {X Y U V : Type u} {A : X → C} {B : Y → C} {D : U → C} {E : V → C}
variable {xs : List X} {ys : List Y} {us : List U} {vs : List V}
variable {a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I} {b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I}
variable {d : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D us ⟶ I} {e : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) E vs ⟶ I}
variable (p : WordAugReadComparison A B xs ys a b) (q : WordAugReadComparison D E us vs d e)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4600000 in
include NR NL hl hr in
noncomputable def WordAugReadComparison.product :
    WordAugReadComparison (crossLabel T A D) (crossLabel T B E) (xs.product us) (ys.product vs)
      (rectangularWordAugCell R L (J.ρ I) A D xs us a d) (rectangularWordAugCell R L (J.ρ I) B E ys vs b e) := by
  let r := Equiv.prodCongr p.read q.read
  let F := crossLabel T A D
  let G := crossLabel T B E
  let s := xs.product us
  let t := ys.product vs
  let φ (z : X × U) : F z ≅ G (r z) :=
    ⟨T.map (p.coefficient z.1).hom (q.coefficient z.2).hom,
     T.map (p.coefficient z.1).inv (q.coefficient z.2).inv, by
       change (coeff (C:=C)).seq _ _ = (coeff (C:=C)).id _
       rw [← T.map_seq, show (coeff (C:=C)).seq (p.coefficient z.1).hom (p.coefficient z.1).inv = _ from
          (p.coefficient z.1).hom_inv_id, show (coeff (C:=C)).seq (q.coefficient z.2).hom (q.coefficient z.2).inv = _ from
          (q.coefficient z.2).hom_inv_id]
       exact T.map_id _ _, by
       change (coeff (C:=C)).seq _ _ = (coeff (C:=C)).id _
       rw [← T.map_seq, show (coeff (C:=C)).seq (p.coefficient z.1).inv (p.coefficient z.1).hom = _ from
          (p.coefficient z.1).inv_hom_id, show (coeff (C:=C)).seq (q.coefficient z.2).inv (q.coefficient z.2).hom = _ from
          (q.coefficient z.2).inv_hom_id]
       exact T.map_id _ _⟩
  let α := rectangularWordAugCell R L (J.ρ I) A D xs us a d
  let β := rectangularWordAugCell R L (J.ρ I) B E ys vs b e

  let y := ys.map p.read.symm
  let v := vs.map q.read.symm
  let pφ := fun x => (p.coefficient x).hom
  let qφ := fun x => (q.coefficient x).hom
  let B₀ := B ∘ p.read
  let E₀ := E ∘ q.read
  let p' := eqToHom ((std_fold_map B p.read y).symm.trans
    (congrArg (fold 𝒮 Zₐ B) (equiv_word_read p.read ys))) ≫ b
  let q' := eqToHom ((std_fold_map E q.read v).symm.trans
    (congrArg (fold 𝒮 Zₐ E) (equiv_word_read q.read vs))) ≫ e
  let τ := rectangularWordAugCell R L (J.ρ I) B₀ E₀ y v p' q'
  let o := rectWordAxisOrder p.order q.order
  have hy : y.map p.read = ys := equiv_word_read p.read ys
  have hv : v.map q.read = vs := equiv_word_read q.read vs
  have ht : (y.product v).map (r ∘ id) = t :=
    (map_product_word p.read q.read y v).trans (congrArg₂ List.product hy hv)
  have k₀ : HEq β τ := by
    have k := rectangleCell_map_heq' R L B E p.read q.read y v hy hv (p:=p') (q:=q')
      (hom_source_pin_heq _ b) (hom_source_pin_heq _ e)
    change HEq (rectWordChart (G ∘ r) y v ≫ independentCell R L B₀ E₀ y v p' q')
      (rectWordChart G ys vs ≫ independentCell R L B E ys vs b e) at k
    let w := (std_fold_map G r (y.product v)).symm.trans (congrArg (fold 𝒮 Zₐ G) ht)
    have hh := structural_seq_heq (K:=coeff (C:=C)) w rfl rfl k
      (HEq.rfl : HEq (J.ρ I) (J.ρ I))
    change HEq ((rectWordChart (G ∘ r) y v ≫ independentCell R L B₀ E₀ y v p' q') ≫ J.ρ I)
      ((rectWordChart G ys vs ≫ independentCell R L B E ys vs b e) ≫ J.ρ I) at hh
    simp only [Category.assoc] at hh
    exact hh.symm
  let pa := AddressOrder.mapSum additiveStructure A p.order
  let qa := AddressOrder.mapSum additiveStructure D q.order
  let p₀ := act 𝒮 Zₐ pφ y
  let q₀ := act 𝒮 Zₐ qφ v
  have hp : pa ≫ p₀ ≫ p' = a := p.preserves
  have hq : qa ≫ q₀ ≫ q' = d := q.preserves
  have h₀ := rectWordChart_axis_order F p.order q.order
  have h₁ := rectWordChart_natural (fun z => (φ z).hom) y v
  have h₂ := independent_gather_order R L A D p.order q.order (fun x => hl (A x)) (hr _)
  have h₃ := rowGather_nat R L y v NR NL pφ qφ
  let j₀ := rectWordChart F xs us
  let δ := AddressOrder.mapSum additiveStructure F o
  let g := rowGather R L A D xs us
  let g' := rowGather R L A D y v
  let t₀ := act 𝒮 Zₐ (fun z => (φ z).hom) (y.product v)
  let n₀ := act 𝒮 Zₐ (fun x => act 𝒮 Zₐ (fun z => T.map (pφ x) (qφ z)) v) y
  let x₀ := act 𝒮 Zₐ (fun x => AddressOrder.mapSum additiveStructure (fun z => T.obj (A x) (D z)) q.order) xs
  let y₀ := AddressOrder.mapSum additiveStructure (fun x => fold 𝒮 Zₐ (fun z => T.obj (A x) (D z)) v) p.order
  change δ ≫ rectWordChart F y v = j₀ ≫ (x₀ ≫ y₀) at h₀
  change t₀ ≫ rectWordChart (G ∘ r) y v = rectWordChart F y v ≫ n₀ at h₁
  change x₀ ≫ y₀ ≫ g' = g ≫ T.map pa qa at h₂
  change n₀ ≫ rowGather R L B₀ E₀ y v = g' ≫ T.map p₀ q₀ at h₃
  have law : δ ≫ t₀ ≫ τ = α := by
    change δ ≫ t₀ ≫ rectWordChart (G ∘ r) y v ≫ (rowGather R L B₀ E₀ y v ≫ T.map p' q') ≫ J.ρ I =
      j₀ ≫ (g ≫ T.map a d) ≫ J.ρ I
    simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₀, reassoc_of% h₃, reassoc_of% h₂]
    have m₀ : T.map pa qa ≫ T.map p₀ q₀ ≫ T.map p' q' = T.map a d := by
      change (coeff (C:=C)).seq (T.map pa qa) ((coeff (C:=C)).seq (T.map p₀ q₀) (T.map p' q')) = _
      rw [← T.map_seq, ← T.map_seq]
      exact congrArg₂ T.map hp hq
    rw [reassoc_of% m₀]
  exact WordAugReadComparison.ofScalarOrder r id s t s (y.product v) (List.map_id s) ht φ α β α τ
    HEq.rfl k₀ o law

end Word

namespace OrderedDependentAugData

set_option backward.isDefEq.respectTransparency false in
include NR NL hl hr in
noncomputable def ReadComparison.product {A B D E : OrderedDependentAugData I}
    (p : ReadComparison A B) (q : ReadComparison D E) :
    ReadComparison (A.product R L J D) (B.product R L J E) where
  parent := p.parent.product R L J NR NL hl hr q.parent
  child z := (p.child z.1).product R L J NR NL hl hr (q.child z.2)

end OrderedDependentAugData
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
