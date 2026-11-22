module
public import ContextualComposition.TaggedPermutation
@[expose] public section

namespace ContextualComposition.NativeFinitePush.DependentFibre
universe w
variable {X : Type w}
namespace AddressOrder
def suffix {xs ys : List X} (r : AddressOrder X xs ys) (zs : List X) :
    AddressOrder X (xs ++ zs) (ys ++ zs) :=
  match r with
  | .ident _ => .ident _
  | .swap a b ts => .swap a b (ts ++ zs)
  | .keep a p => .keep a (p.suffix zs)
  | .seq p q => .seq (p.suffix zs) (q.suffix zs)
def prepend (zs : List X) {xs ys : List X} (r : AddressOrder X xs ys) :
    AddressOrder X (zs ++ xs) (zs ++ ys) :=
  match zs with
  | [] => r
  | z::ts => .keep z (prepend ts r)
def parallel {xs ys xs' ys' : List X}
    (r : AddressOrder X xs xs') (s : AddressOrder X ys ys') :
    AddressOrder X (xs ++ ys) (xs' ++ ys') :=
  .seq (r.suffix ys) (prepend xs' s)
end AddressOrder
end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X : Type w} (A : X → C)
local notation "𝔉" => fold (binary (Additive.sum (Additive.ofBraided (C:=C)))) (𝟙_ C) A
local notation "route" => AddressOrder.mapSum (additiveStructure (C:=C)) A
local notation "split" => join (additiveStructure (C:=C)) A

theorem std_join_nil (ys : List X) : split [] ys = (λ_ (𝔉 ys)).inv := rfl
theorem std_join_cons (x : X) (xs ys : List X) :
    split (x::xs) ys = (A x ◁ split xs ys) ≫ (α_ (A x) (𝔉 xs) (𝔉 ys)).inv := by
  change ((𝟙 (A x) ⊗ₘ split xs ys) ≫ (α_ (A x) (𝔉 xs) (𝔉 ys)).inv) = _
  rw [id_tensorHom]

set_option backward.isDefEq.respectTransparency false in
theorem std_join_prefix {ys ys' : List X} (xs : List X) (r : AddressOrder X ys ys') :
    route (AddressOrder.prepend xs r) ≫ split xs ys' = split xs ys ≫ 𝔉 xs ◁ route r := by
  induction xs with
  | nil =>
    change route r ≫ (λ_ (𝔉 ys')).inv = (λ_ (𝔉 ys)).inv ≫ 𝟙_ C ◁ route r
    rw [leftUnitor_inv_naturality]
  | cons a xs ih =>
    rw [std_join_cons, std_join_cons]
    change (𝟙 (A a) ⊗ₘ route (AddressOrder.prepend xs r)) ≫
      (A a ◁ split xs ys') ≫ (α_ (A a) (𝔉 xs) (𝔉 ys')).inv =
        ((A a ◁ split xs ys) ≫ (α_ (A a) (𝔉 xs) (𝔉 ys)).inv) ≫
          ((A a ⊗ 𝔉 xs) ◁ route r)
    rw [id_tensorHom, ← whiskerLeft_comp_assoc, ih, whiskerLeft_comp,
      Category.assoc, Category.assoc, associator_inv_naturality_right]

private theorem std_route_swap (a b : X) (ts : List X) :
    route (.swap a b ts) = crossHead (A a) (A b) (𝔉 ts) := by
  change (α_ (A a) (A b) (𝔉 ts)).inv ≫ ((β_ (A a) (A b)).hom ⊗ₘ 𝟙 (𝔉 ts)) ≫
    (α_ (A b) (A a) (𝔉 ts)).hom = _
  rw [tensorHom_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem std_join_suffix {xs xs' : List X} (r : AddressOrder X xs xs') (ys : List X) :
    route (r.suffix ys) ≫ split xs' ys = split xs ys ≫ route r ▷ 𝔉 ys := by
  induction r with
  | ident xs =>
    change 𝟙 _ ≫ split xs ys = split xs ys ≫ 𝟙 _ ▷ 𝔉 ys
    rw [id_whiskerRight, Category.id_comp]
    exact (Category.comp_id _).symm
  | swap a b ts =>
    simp only [AddressOrder.suffix, std_route_swap, std_join_cons]

    let z := 𝔉 ys
    let t := 𝔉 ts
    let J : 𝔉 (ts ++ ys) ⟶ t ⊗ z := split ts ys
    have h := crossHead_nat (A a) (A b) J
    calc
      _ = ((A a ◁ A b ◁ J) ≫ crossHead (A a) (A b) (t ⊗ z)) ≫
          (A b ◁ (α_ (A a) t z).inv) ≫ (α_ (A b) (A a ⊗ t) z).inv := by
        rw [← h]
        monoidal
      _ = _ := by unfold crossHead; monoidal
  | keep a p ih =>
    rw [std_join_cons, std_join_cons]
    change (𝟙 (A a) ⊗ₘ route (p.suffix ys)) ≫
      (A a ◁ split _ ys) ≫ (α_ _ _ _).inv =
      ((A a ◁ split _ ys) ≫ (α_ _ _ _).inv) ≫ (𝟙 (A a) ⊗ₘ route p) ▷ 𝔉 ys
    rw [id_tensorHom, ← whiskerLeft_comp_assoc, ih, whiskerLeft_comp]
    monoidal
  | seq p q hp hq =>
    change (route (p.suffix ys) ≫ route (q.suffix ys)) ≫ split _ ys =
      split _ ys ≫ (route p ≫ route q) ▷ 𝔉 ys
    rw [Category.assoc, hq, ← Category.assoc, hp, Category.assoc, comp_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
theorem std_join_parallel {xs ys xs' ys' : List X}
    (r : AddressOrder X xs xs') (s : AddressOrder X ys ys') :
    route (r.parallel s) ≫ split xs' ys' = split xs ys ≫ (route r ⊗ₘ route s) := by
  change (route (r.suffix ys) ≫ route (AddressOrder.prepend xs' s)) ≫ split xs' ys' =
    split xs ys ≫ (route r ⊗ₘ route s)
  rw [Category.assoc, std_join_prefix, ← Category.assoc, std_join_suffix, Category.assoc, tensorHom_def]



private theorem std_fold_cons (x : X) (xs : List X) : 𝔉 (x::xs) = A x ⊗ 𝔉 xs := rfl

private theorem std_fold_append_assoc_cons (x : X) (xs ys zs : List X) :
    eqToHom (congrArg 𝔉 (List.append_assoc (x::xs) ys zs)) =
      A x ◁ eqToHom (congrArg 𝔉 (List.append_assoc xs ys zs)) := by
  rw [whiskerLeft_eqToHom]
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem std_join_assoc (xs ys zs : List X) :
    eqToHom (congrArg 𝔉 (List.append_assoc xs ys zs)) ≫ split xs (ys ++ zs) ≫ 𝔉 xs ◁ split ys zs =
      split (xs ++ ys) zs ≫ split xs ys ▷ 𝔉 zs ≫ (α_ (𝔉 xs) (𝔉 ys) (𝔉 zs)).hom := by
  induction xs with
  | nil =>
    simp only [List.nil_append, std_join_nil, eqToHom_refl, Category.id_comp]
    let J : 𝔉 (ys ++ zs) ⟶ 𝔉 ys ⊗ 𝔉 zs := split ys zs
    change (λ_ (𝔉 (ys ++ zs))).inv ≫ 𝟙_ C ◁ J =
      J ≫ (λ_ (𝔉 ys)).inv ▷ 𝔉 zs ≫ (α_ (𝟙_ C) (𝔉 ys) (𝔉 zs)).hom
    rw [← leftUnitor_inv_naturality]
    monoidal
  | cons a xs ih =>
    simp only [std_fold_append_assoc_cons, List.cons_append, std_join_cons, std_fold_cons]
    have h := congrArg (fun f => A a ◁ f) ih
    calc
      _ = (A a ◁ (eqToHom (congrArg 𝔉 (List.append_assoc xs ys zs)) ≫
          split xs (ys ++ zs) ≫ 𝔉 xs ◁ split ys zs)) ≫
          (α_ (A a) (𝔉 xs) (𝔉 ys ⊗ 𝔉 zs)).inv := by monoidal
      _ = _ := by rw [h]; monoidal

/-- Leaf labels remain addresses. An explicit nullary node has no addresses;
an atomic coefficient equal to the unit still has one address. -/
inductive SumTree (X : Type w) where
  | zero
  | atom (x : X)
  | plus (l r : SumTree X)

namespace SumTree
def leaves : SumTree X → List X
  | .zero => []
  | .atom x => [x]
  | .plus l r => l.leaves ++ r.leaves

def word : List X → SumTree X
  | [] => .zero
  | x::xs => .plus (.atom x) (word xs)

def eval : SumTree X → C
  | .zero => 𝟙_ C
  | .atom x => A x
  | .plus l r => eval l ⊗ eval r

theorem word_leaves (xs : List X) : (word xs).leaves = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [word, leaves, ih, List.singleton_append]

def chart : (t : SumTree X) → 𝔉 t.leaves ⟶ eval A t
  | .zero => 𝟙 _
  | .atom x => (ρ_ (A x)).hom
  | .plus l r => split l.leaves r.leaves ≫ (chart l ⊗ₘ chart r)

def stdAddInvertible : AddInvertible (additiveStructure (C:=C)) where
  unit a := ⟨(λ_ a).hom, (λ_ a).inv_hom_id, (λ_ a).hom_inv_id⟩
  assoc a b c := ⟨(α_ a b c).inv, (α_ a b c).hom_inv_id, (α_ a b c).inv_hom_id⟩
  assocInv a b c := ⟨(α_ a b c).hom, (α_ a b c).inv_hom_id, (α_ a b c).hom_inv_id⟩
  swap a b := ⟨(β_ a b).inv, (β_ a b).hom_inv_id, (β_ a b).inv_hom_id⟩

def chartInv : (t : SumTree X) → Inv (K:=coeff (C:=C)) (chart A t)
  | .zero => Inv.ident _
  | .atom x => ⟨(ρ_ (A x)).inv, (ρ_ (A x)).hom_inv_id, (ρ_ (A x)).inv_hom_id⟩
  | .plus l r => (joinInv stdAddInvertible A l.leaves r.leaves).comp ((chartInv l).tensor (T:=binary (Additive.ofBraided (C:=C)).sum) (chartInv r))

def changeChart {t s : SumTree X} (p : AddressOrder X t.leaves s.leaves) :
    eval A t ⟶ eval A s :=
  (chartInv A t).inv ≫ route p ≫ chart A s

theorem changeChart_comp {t s q : SumTree X} (p : AddressOrder X t.leaves s.leaves)
    (r : AddressOrder X s.leaves q.leaves) :
    changeChart A p ≫ changeChart A r = changeChart A (.seq p r) := by
  have h : chart A s ≫ (chartInv A s).inv = 𝟙 (𝔉 s.leaves) := (chartInv A s).hi
  unfold changeChart
  change _ = (chartInv A t).inv ≫ (route p ≫ route r) ≫ chart A q
  simp only [Category.assoc, reassoc_of% h]

theorem changeChart_id (t : SumTree X) :
    changeChart A (.ident t.leaves) = 𝟙 (eval A t) := by
  have h : (chartInv A t).inv ≫ chart A t = 𝟙 (eval A t) := (chartInv A t).ih
  change (chartInv A t).inv ≫ 𝟙 _ ≫ chart A t = _
  rw [Category.id_comp]
  exact h

theorem changeChart_coherent {t s : SumTree X} (hn : t.leaves.Nodup)
    (p q : AddressOrder X t.leaves s.leaves) :
    changeChart A p = changeChart A q :=
  congrArg (fun f => (chartInv A t).inv ≫ f ≫ chart A s) (tagged_permutation_coherent A hn p q)

theorem chart_changeChart {t s : SumTree X} (p : AddressOrder X t.leaves s.leaves) :
    chart A t ≫ changeChart A p = route p ≫ chart A s := by
  have h : chart A t ≫ (chartInv A t).inv = 𝟙 (𝔉 t.leaves) := (chartInv A t).hi
  unfold changeChart
  rw [← Category.assoc, h, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem changeChart_parallel {t₁ t₂ s₁ s₂ : SumTree X}
    (p : AddressOrder X t₁.leaves s₁.leaves) (q : AddressOrder X t₂.leaves s₂.leaves) :
    changeChart A (t:=.plus t₁ t₂) (s:=.plus s₁ s₂) (p.parallel q) =
      changeChart A p ⊗ₘ changeChart A q := by
  apply (chartInv A (.plus t₁ t₂)).cancelL
  change chart A (.plus t₁ t₂) ≫ _ = chart A (.plus t₁ t₂) ≫ _
  rw [chart_changeChart]
  change route (p.parallel q) ≫ (split s₁.leaves s₂.leaves ≫ (chart A s₁ ⊗ₘ chart A s₂)) =
    (split t₁.leaves t₂.leaves ≫ (chart A t₁ ⊗ₘ chart A t₂)) ≫ _
  rw [← Category.assoc, std_join_parallel, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, chart_changeChart, chart_changeChart]

set_option backward.isDefEq.respectTransparency false in
theorem chart_left_unit (t : SumTree X) :
    chart A (.plus .zero t) ≫ (λ_ (eval A t)).hom = chart A t := by
  let P : 𝔉 t.leaves ⟶ eval A t := chart A t
  change ((λ_ (𝔉 t.leaves)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ P)) ≫ (λ_ (eval A t)).hom = P
  rw [id_tensorHom, Category.assoc, leftUnitor_naturality, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem chart_assoc (t s q : SumTree X) :
    chart A (.plus (.plus t s) q) ≫ (α_ (eval A t) (eval A s) (eval A q)).hom =
      eqToHom (congrArg 𝔉 (List.append_assoc t.leaves s.leaves q.leaves)) ≫
        chart A (.plus t (.plus s q)) := by
  let X₁ := 𝔉 t.leaves
  let X₂ := 𝔉 s.leaves
  let X₃ := 𝔉 q.leaves
  let j₁ : 𝔉 (t.leaves ++ s.leaves) ⟶ X₁ ⊗ X₂ := split t.leaves s.leaves
  let j₂ : 𝔉 (s.leaves ++ q.leaves) ⟶ X₂ ⊗ X₃ := split s.leaves q.leaves
  let P := chart A t
  let Q := chart A s
  let R := chart A q
  change (split (t.leaves ++ s.leaves) q.leaves ≫ ((j₁ ≫ (P ⊗ₘ Q)) ⊗ₘ R)) ≫ _ =
    _ ≫ split t.leaves (s.leaves ++ q.leaves) ≫ (P ⊗ₘ (j₂ ≫ (Q ⊗ₘ R)))
  calc
    _ = (split (t.leaves ++ s.leaves) q.leaves ≫ j₁ ▷ X₃ ≫
          (α_ X₁ X₂ X₃).hom) ≫ (P ⊗ₘ (Q ⊗ₘ R)) := by
      have f : ((j₁ ≫ (P ⊗ₘ Q)) ⊗ₘ R) = (j₁ ▷ X₃) ≫ ((P ⊗ₘ Q) ⊗ₘ R) := by
        rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
      rw [f]
      simp only [Category.assoc, associator_naturality]
    _ = _ := by
      have h := std_join_assoc A t.leaves s.leaves q.leaves
      change _ = split (t.leaves ++ s.leaves) q.leaves ≫ j₁ ▷ X₃ ≫ (α_ X₁ X₂ X₃).hom at h
      rw [← h]
      have f : (P ⊗ₘ (j₂ ≫ (Q ⊗ₘ R))) = (X₁ ◁ j₂) ≫ (P ⊗ₘ (Q ⊗ₘ R)) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
      rw [f]
      simp only [Category.assoc]
      rfl


def mapTree {A B : X → C} (p : ∀ x, A x ⟶ B x) :
    (t : SumTree X) → eval A t ⟶ eval B t
  | .zero => 𝟙 _
  | .atom x => p x
  | .plus l r => mapTree p l ⊗ₘ mapTree p r

set_option backward.isDefEq.respectTransparency false in
theorem chart_natural {A B : X → C} (p : ∀ x, A x ⟶ B x) (t : SumTree X) :
    act (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) p t.leaves ≫ chart B t =
      chart A t ≫ mapTree p t := by
  induction t with
  | zero => rfl
  | atom x =>
    change (p x ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (B x)).hom = (ρ_ (A x)).hom ≫ p x
    rw [tensorHom_id, rightUnitor_naturality]
  | plus l r ihL ihR =>
    let S := binary (Additive.ofBraided (C:=C)).sum
    have e := act_append (S:=S) additiveNaturality p l.leaves r.leaves
    change act S (𝟙_ C) p (l.leaves ++ r.leaves) ≫ join additiveStructure B l.leaves r.leaves =
      join additiveStructure A l.leaves r.leaves ≫
        (act S (𝟙_ C) p l.leaves ⊗ₘ act S (𝟙_ C) p r.leaves) at e
    change act S (𝟙_ C) p (l.leaves ++ r.leaves) ≫ (_ ≫ (chart B l ⊗ₘ chart B r)) =
      (_ ≫ (chart A l ⊗ₘ chart A r)) ≫ (mapTree p l ⊗ₘ mapTree p r)
    rw [← Category.assoc, e, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, ihL, ihR]

set_option backward.isDefEq.respectTransparency false in
theorem changeChart_natural {A B : X → C} (p : ∀ x, A x ⟶ B x) {t s : SumTree X}
    (r : AddressOrder X t.leaves s.leaves) :
    mapTree p t ≫ changeChart B r = changeChart A r ≫ mapTree p s := by
  apply (chartInv A t).cancelL
  change chart A t ≫ _ = chart A t ≫ _
  let S := binary (Additive.ofBraided (C:=C)).sum
  have h₁ : act S (𝟙_ C) p t.leaves ≫ AddressOrder.mapSum additiveStructure B r =
      AddressOrder.mapSum additiveStructure A r ≫ act S (𝟙_ C) p s.leaves :=
    AddressOrder.natural additiveNaturality p r
  rw [← Category.assoc, ← chart_natural, Category.assoc, chart_changeChart,
    ← Category.assoc, h₁, ← Category.assoc, chart_changeChart, Category.assoc,
    Category.assoc, chart_natural]

end SumTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
