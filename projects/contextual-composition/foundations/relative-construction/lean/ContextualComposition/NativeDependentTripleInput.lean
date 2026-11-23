module
public import ContextualComposition.NativeDependentAssociatorCells
@[expose] public section

/-! Construct both actual native ternary aggregation maps independently. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

variable {X Y W X' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : X → List Y} {ws : X → Y → List W}
variable {xs' : List X'} {ys' : X' → List Y'} {ws' : X' → Y' → List W'}
variable {V : X → C} {B : X → Y → C} {D : X → Y → W → C}
variable {V' : X' → C} {B' : X' → Y' → C} {D' : X' → Y' → W' → C}
variable (F : OrderedDependentMap xs ys xs' ys' V B V' B')

structure OrderedThirdMap
    (ws : X → Y → List W) (ws' : X' → Y' → List W')
    (D : X → Y → W → C) (D' : X' → Y' → W' → C) where
  leaf : X → Y → W → W'
  support : ∀ x ∈ xs, ∀ y ∈ ys x, ∀ z ∈ ws x y,
    leaf x y z ∈ ws' (F.parent x) (F.child x y)
  cell : ∀ x ∈ xs, ∀ y ∈ ys x, ∀ z ∈ ws' (F.parent x) (F.child x y),
    fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (wordFibre (ws x y) (leaf x y) z) ⟶
      D' (F.parent x) (F.child x y) z

variable (G : OrderedThirdMap F ws ws' D D')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

namespace OrderedThirdMap

/-- The upper two layers are accumulated first to form the outer
whole-fibre maps of the final application of unary accumulation. -/
def leftInput :
    OrderedDependentMap (dependentWord xs ys) (fun t => ws t.1 t.2)
      (dependentWord xs' ys') (fun t => ws' t.1 t.2)
      (dependentLabels (T:=T) V B) (fun p => D p.1 p.2)
      (dependentLabels (T:=T) V' B') (fun p => D' p.1 p.2) where
  parent := origDepCarrier F
  child t := G.leaf t.1 t.2
  parent_mem := origDepCarrier_support F
  child_mem t ht k hk := by
    have h := (dependentWord_mem xs ys t).mp ht
    exact G.support _ h.1 _ h.2 k hk
  outer := origDependentCell F R L
  inner t ht k hk := by
    have h := (dependentWord_mem xs ys t).mp ht
    exact G.cell _ h.1 _ h.2 k hk

/-- At each *original* source parent, accumulate its middle and leaf
maps. This input lives before the potentially many-to-one parent merge. -/
def tailInput (x : X) (hx : x ∈ xs) :
    OrderedDependentMap (ys x) (ws x) (ys' (F.parent x)) (ws' (F.parent x))
      (B x) (D x) (B' (F.parent x)) (D' (F.parent x)) where
  parent := F.child x
  child := G.leaf x
  parent_mem := F.child_mem x hx
  child_mem := G.support x hx
  outer := F.inner x hx
  inner := G.cell x hx

def rightInput :
    OrderedDependentMap xs (fun x => dependentWord (ys x) (ws x))
      xs' (fun x => dependentWord (ys' x) (ws' x))
      V (fun x => dependentLabels (T:=T) (B x) (D x))
      V' (fun x => dependentLabels (T:=T) (B' x) (D' x)) where
  parent := F.parent
  child x t := (F.child x t.1,G.leaf x t.1 t.2)
  parent_mem := F.parent_mem
  child_mem x hx := origDepCarrier_support (G.tailInput F x hx)
  outer := F.outer
  inner x hx := origDependentCell (G.tailInput F x hx) R L

theorem associator_carrier (t : (X × Y) × W) :
    tripleRetag (origDepCarrier (G.leftInput F R L) t) =
      origDepCarrier (G.rightInput F R L) (tripleRetag t) := rfl

noncomputable def leafNative (x : X) (hx : x ∈ xs) (y : Y) (hy : y ∈ ys x)
    (h : (ws' (F.parent x) (F.child x y)).Nodup) :
    Hom ℙ (wordFamily (D x y) (ws x y))
      (wordFamily (D' (F.parent x) (F.child x y)) (ws' (F.parent x) (F.child x y))) :=
  wordNativeMap (G.leaf x y) (G.support x hx y hy) h (D x y) (D' (F.parent x) (F.child x y))
    (fun z => G.cell x hx y hy (ws' (F.parent x) (F.child x y))[z] (List.getElem_mem _))

structure Preserves {I : C}
    (h : ∀ x ∈ xs, ∀ y ∈ ys x, (ws' (F.parent x) (F.child x y)).Nodup)
    (γ : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (ws x y) ⟶ I)
    (γ' : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D' x y) (ws' x y) ⟶ I) : Prop where
  leaf (x : X) (hx : x ∈ xs) (y : Y) (hy : y ∈ ys x) :
    (G.leafNative F x hx y hy (h x hx y hy)).comp
      (wordAug (D' (F.parent x) (F.child x y)) (ws' (F.parent x) (F.child x y)) (γ' (F.parent x) (F.child x y))).ε =
    (wordAug (D x y) (ws x y) (γ x y)).ε

section Aug
variable {I : C} (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L)
variable [DecidableEq X] [DecidableEq Y]
variable (hx : xs.Nodup) (hx' : xs'.Nodup)
variable (hy : ∀ x ∈ xs, (ys x).Nodup) (hy' : ∀ x ∈ xs', (ys' x).Nodup)
variable (hw : ∀ x ∈ xs, ∀ y ∈ ys x, (ws x y).Nodup)
variable (hw' : ∀ x ∈ xs', ∀ y ∈ ys' x, (ws' x y).Nodup)
variable {ε : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V xs ⟶ I}
variable {ε' : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V' xs' ⟶ I}
variable {δ : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B x) (ys x) ⟶ I}
variable {δ' : ∀ x, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (B' x) (ys' x) ⟶ I}
variable {γ : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D x y) (ws x y) ⟶ I}
variable {γ' : ∀ x y, fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (D' x y) (ws' x y) ⟶ I}
variable (p : F.Preserves hx' (fun x hx => hy' _ (F.parent_mem x hx)) δ δ' ε ε')
variable (q : G.Preserves F (fun x hx y hy => hw' _ (F.parent_mem x hx) _ (F.child_mem x hx y hy)) γ γ')

include N NL hl hx hy p q in
set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq Y] in
theorem leftPreserves :
    (G.leftInput F R L).Preserves (dependentWord_nodup hx' hy')
      (fun x h => let hh := (dependentWord_mem xs ys x).mp h
        hw' _ (F.parent_mem _ hh.1) _ (F.child_mem _ hh.1 _ hh.2))
      (fun x => γ x.1 x.2) (fun x => γ' x.1 x.2)
      (dependentWordAugCell R L J xs ys V B (indexedAugmentation δ) ε)
      (dependentWordAugCell R L J xs' ys' V' B' (indexedAugmentation δ') ε') where
  outer := unaryPreserves_of_orderedInputs F R L J N NL hl hx hx' hy hy' p
  inner t ht :=
    let h := (dependentWord_mem xs ys t).mp ht
    q.leaf t.1 h.1 t.2 h.2

include N NL hl hy hw p q in
set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq X] in
theorem rightPreserves :
    (G.rightInput F R L).Preserves hx'
      (fun x h => dependentWord_nodup (hy' _ (F.parent_mem x h)) (hw' _ (F.parent_mem x h)))
      (fun x => dependentWordAugCell R L J (ys x) (ws x) (B x) (D x) (indexedAugmentation (γ x)) (δ x))
      (fun x => dependentWordAugCell R L J (ys' x) (ws' x) (B' x) (D' x) (indexedAugmentation (γ' x)) (δ' x))
      ε ε' where
  outer := p.outer
  inner x h := by
    let P := G.tailInput F x h
    have htail : P.Preserves (hy' _ (F.parent_mem x h))
        (fun y hy => hw' _ (F.parent_mem x h) _ (F.child_mem x h y hy))
        (γ x) (γ' (F.parent x)) (δ x) (δ' (F.parent x)) :=
      ⟨p.inner x h, fun y hy => q.leaf x h y hy⟩
    exact unaryPreserves_of_orderedInputs P R L J N NL hl
      (hy x h) (hy' _ (F.parent_mem x h)) (hw x h) (hw' _ (F.parent_mem x h)) htail

set_option backward.isDefEq.respectTransparency false in
noncomputable def leftAugMap :
    AugHom ℙ (dependentAssocLeft R L J xs ys ws V B D ε δ γ)
      (dependentAssocLeft R L J xs' ys' ws' V' B' D' ε' δ' γ') :=
  OrderedDependentMap.accumulateAug R L J (G.leftInput F R L) N NL hl
    (dependentWord_nodup hx hy) (dependentWord_nodup hx' hy')
    (fun t ht => let m := (dependentWord_mem xs ys t).mp ht; hw _ m.1 _ m.2)
    (fun t ht => let m := (dependentWord_mem xs' ys' t).mp ht; hw' _ m.1 _ m.2)
    (leftPreserves F G R L J N NL hl hx hx' hy hy' hw' p q)

set_option backward.isDefEq.respectTransparency false in
noncomputable def rightAugMap :
    AugHom ℙ (dependentAssocRight R L J xs ys ws V B D ε δ γ)
      (dependentAssocRight R L J xs' ys' ws' V' B' D' ε' δ' γ') :=
  OrderedDependentMap.accumulateAug R L J (G.rightInput F R L) N NL hl hx hx'
    (fun x h => dependentWord_nodup (hy x h) (hw x h))
    (fun x h => dependentWord_nodup (hy' x h) (hw' x h))
    (rightPreserves F G R L J N NL hl hx' hy hy' hw hw' p q)

end Aug
end OrderedThirdMap
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
