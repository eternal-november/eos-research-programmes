module
public import ContextualComposition.NativeFubiniReadAug
@[expose] public section

/-! The binary Fubini isomorphism supplies the actual ordered
preservation input needed to whisker it in a surrounding dependent
augmentation. The order is recovered from its tagged singleton trace. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

structure WordAugReadComparison {X Y : Type u} {I : C} (A : X → C) (B : Y → C)
    (xs : List X) (ys : List Y) (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I) where
  read : X ≃ Y
  order : AddressOrder X xs (ys.map read.symm)
  coefficient : ∀ x, A x ≅ B (read x)
  preserves :
    let e := (std_fold_map B read (ys.map read.symm)).symm.trans
      (congrArg (fold 𝒮 Zₐ B) (equiv_word_read read ys))
    AddressOrder.mapSum additiveStructure A order ≫ act 𝒮 Zₐ (fun x => (coefficient x).hom) (ys.map read.symm) ≫
      eqToHom e ≫ b = a

set_option backward.isDefEq.respectTransparency false in
noncomputable def WordAugReadComparison.ofTrace {X Y : Type u} {I : C} {A : X → C} {B : Y → C}
    (f : X ≃ Y) (xs : List X) (ys : List Y) (hx : xs.Nodup) (hy : ys.Nodup)
    (φ : ∀ x, A x ≅ B (f x))
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (v : NativeAugmentedIso (wordAug A xs a) (wordAug B ys b))
    (h : RawSingletonTrace (rawWordFrame A xs hx)
      ((rawWordFrame B ys hy).relabel f.symm f.symm.injective (B ∘ f)
        (fun x => congrArg B (f.apply_symm_apply x).symm))
      (fun x => (φ x).hom) v.hom.native) :
    WordAugReadComparison A B xs ys a b := by
  let o := Classical.choice (AddressOrder.ofPerm (rawSingletonTrace_read_perm A B f xs ys hx hy φ v h))
  exact ⟨f,o,φ,wordReadAugIso_preserves A B f xs ys hx hy φ a b v h o⟩

namespace OrderedDependentAugData
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (A B : OrderedDependentAugData I)
local notation "A₀" => dependentLabels (T:=T) A.V A.A
local notation "B₀" => dependentLabels (T:=T) B.V B.A
local notation "wA" => dependentWord A.xs A.us
local notation "wB" => dependentWord B.xs B.us
local notation "AB" => A.product R L J B

def accCell :=
  dependentWordAugCell R L J A.xs A.us A.V A.A (indexedAugmentation A.δ) A.ε

def separatePairCell :=
  rectangularWordAugCell R L (J.ρ I) A₀ B₀ wA wB (accCell R L J A) (accCell R L J B)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3400000 in
noncomputable def binaryFubini_wordComparison :
    WordAugReadComparison
      (crossLabel T A₀ B₀) (dependentLabels (T:=T) (AB).V (AB).A)
      ((wA).product wB) (dependentWord (AB).xs (AB).us)
      (separatePairCell R L J A B) (accCell R L J AB) := by
  let D := A.product R L J B
  let F := crossLabel T A₀ B₀
  let G := dependentLabels (T:=T) D.V D.A
  let xs := (wA).product wB
  let ys := dependentWord D.xs D.us
  let r := jointRead A B
  let f := r.symm
  let a := separatePairCell R L J A B
  let b := accCell R L J D
  let g := A.binaryFubini R L J N NR NL hl hr m mi h j unit_middle B
  let hA := dependentWord_nodup A.xs_unique A.us_unique
  let hB := dependentWord_nodup B.xs_unique B.us_unique
  let hx := nodup_product_word hA hB
  let hy := dependentWord_nodup D.xs_unique D.us_unique
  let x₀ := rawWordFrame F xs hx
  let x₁ := (A.accFrame R L J).tensor T (B.accFrame R L J)
  let y₀ := (rawWordFrame G ys hy).relabel f.symm f.symm.injective (G ∘ f)
    (fun x => congrArg G (f.apply_symm_apply x).symm)
  let y₁ := A.jointFrame R L J B
  let φ (z : A.Branch × B.Branch) : F z ≅ G (f z) :=
    binaryLeafIso A.V B.V A.A B.A m mi (pairQuad z)
  let e := independentAug_ordered_eq R L (J.ρ I) A₀ B₀ wA wB (accCell R L J A) (accCell R L J B)
  let g₀ := g.retarget e rfl
  have htrace := A.binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr B
  have eh : (independentFamily T (wordFamily A₀ wA) (wordFamily B₀ wB)) = wordFamily F xs :=
    independentFamily_word (T:=T) A₀ B₀ wA wB
  have readEq (i : Fin _) : x₁.read i = x₀.read (Fin.cast (congrArg Family.n eh) i) :=
    frame_tensor_read_cast (rawWordFrame A₀ wA hA) (rawWordFrame B₀ wB hB) rfl rfl
      (fun _ => rfl) (fun _ => rfl) i
  have H : RawSingletonTrace x₀ y₀ (fun z => (φ z).hom) g₀.hom.native :=
    htrace.retarget eh rfl (NativeAugmentedIso.retarget_native_heq g e rfl).symm readEq (fun _ => rfl) (fun _ => HEq.rfl)
  exact WordAugReadComparison.ofTrace f xs ys hx hy φ a b g₀ H

end OrderedDependentAugData


set_option backward.isDefEq.respectTransparency false in
noncomputable def WordAugReadComparison.ident {X : Type u} {I : C} (A : X → C) (xs : List X)
    (a : fold 𝒮 Zₐ A xs ⟶ I) (hn : xs.Nodup) :
    WordAugReadComparison A A xs xs a a := by
  let F := rawWordFrame A xs hn
  exact WordAugReadComparison.ofTrace (Equiv.refl X) xs xs hn hn (fun x => Iso.refl (A x)) a a
    (NativeAugmentedIso.ident (wordAug A xs a))
    ((RawSingletonTrace.ident F).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl))

namespace OrderedDependentAugData
variable {I : C}

structure ReadComparison (A B : OrderedDependentAugData I) where
  parent : WordAugReadComparison A.V B.V A.xs B.xs A.ε B.ε
  child (x : A.X) : WordAugReadComparison (A.A x) (B.A (parent.read x))
    (A.us x) (B.us (parent.read x)) (A.δ x) (B.δ (parent.read x))

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I) (NL : GatherLeftNat L)
variable [lF : ∀ x : C, (leftFactor T x).LaxBraided] (hl : ∀ x : C, SameLeftGather T x L)

set_option backward.isDefEq.respectTransparency false in
noncomputable def ReadComparison.accumulate {A B : OrderedDependentAugData I} (p : ReadComparison A B) :
    NativeAugmentedIso (A.accumulate R L J) (B.accumulate R L J) :=
  dependentOrderedReadIso R L J NL p.parent.read (fun x => (p.child x).read) p.parent.order
    (fun x => (p.child x).order) A.ε B.ε A.δ B.δ p.parent.coefficient (fun x => (p.child x).coefficient)
    (fun x => hl (B.V x)) p.parent.preserves (fun x => (p.child x).preserves)
    (dependentWord_nodup A.xs_unique A.us_unique)

set_option backward.isDefEq.respectTransparency false in
theorem ReadComparison.accumulate_trace {A B : OrderedDependentAugData I} (p : ReadComparison A B)
    {Ω : Type u} (f : A.Branch → Ω) (g : B.Branch → Ω)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (coh : ∀ t : A.Branch, f t = g (p.parent.read t.1,(p.child t.1).read t.2))
    (V W : Ω → C) (eV : ∀ t, (A.accFrame R L J).label t = V (f t))
    (eW : ∀ t, (B.accFrame R L J).label t = W (g t))
    (m : ∀ t, V t ⟶ W t)
    (hm : ∀ t : A.Branch, HEq (T.map (p.parent.coefficient t.1).hom ((p.child t.1).coefficient t.2).hom) (m (f t))) :
    RawSingletonTrace ((A.accFrame R L J).relabel f hf V eV)
      ((B.accFrame R L J).relabel g hg W eW) m (p.accumulate R L J NL hl).hom.native := by
  unfold ReadComparison.accumulate accFrame
  exact dependentOrderedReadIso_trace R L J NL p.parent.read (fun x => (p.child x).read)
    p.parent.order (fun x => (p.child x).order) A.ε B.ε A.δ B.δ p.parent.coefficient (fun x => (p.child x).coefficient)
    (fun x => hl (B.V x)) p.parent.preserves (fun x => (p.child x).preserves)
    (dependentWord_nodup A.xs_unique A.us_unique) (dependentWord_nodup B.xs_unique B.us_unique)
    f g hf hg coh V W eV eW m hm

end OrderedDependentAugData

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
