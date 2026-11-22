module
public import ContextualComposition.OccurrenceAssoc

@[expose] public section
/-! Normalize a program of adjacent exchanges by extracting tagged
occurrences. The deleted occurrence is an address, not a coefficient. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {X : Type w}

/-- Pick a particular occurrence, retaining the full address word without it. -/
inductive Pick (x : X) : List X → List X → Type w
  | here (xs : List X) : Pick x (x::xs) xs
  | next (y : X) {xs ys : List X} : Pick x xs ys → Pick x (y::xs) (y::ys)

namespace Pick
def address {x : X} {xs ys : List X} : Pick x xs ys → AddressOrder X xs (x::ys)
  | .here xs => .ident (x::xs)
  | .next y p => .seq (.keep y p.address) (.swap y x _)

theorem mem {x : X} {xs ys : List X} (p : Pick x xs ys) : x ∈ xs := by
  induction p with
  | here => exact List.mem_cons_self
  | next _ _ ih => exact List.mem_cons_of_mem _ ih

theorem unique {x : X} {xs : List X} (hn : xs.Nodup)
    (p : Σ ys, Pick x xs ys) : ∀ q : Σ ys, Pick x xs ys, p = q := by
  obtain ⟨ys,p⟩ := p
  induction p with
  | here xs =>
    rintro ⟨_,q⟩
    cases q with
    | here => rfl
    | next _ q => exact ((List.nodup_cons.mp hn).1 q.mem).elim
  | @next y xs ys p ih =>
    rintro ⟨_,q⟩
    cases q with
    | here => exact ((List.nodup_cons.mp hn).1 p.mem).elim
    | next y q =>
      exact congrArg (fun a : Σ ts, Pick x xs ts =>
        (⟨y :: a.1, .next y a.2⟩ : Σ ts, Pick x (y::xs) ts))
        (ih (List.nodup_cons.mp hn).2 ⟨_,q⟩)
end Pick

namespace AddressOrder
/-- Pull back a distinguished occurrence along a program, and delete it
from the program. This is constructive and does not inspect labels. -/
def pull {x : X} {xs ys ys' : List X} (r : AddressOrder X xs ys) (p : Pick x ys ys') :
    Σ xs', Pick x xs xs' × AddressOrder X xs' ys' :=
  match r with
  | .ident _ => ⟨_,p,.ident _⟩
  | .swap a b _ =>
    match p with
    | .here _ => ⟨_, .next a (.here _), .ident _⟩
    | .next _ (.here _) => ⟨_, .here _, .ident _⟩
    | .next _ (.next _ q) => ⟨_, .next a (.next b q), .swap a b _⟩
  | .keep a r =>
    match p with
    | .here _ => ⟨_, .here _, r⟩
    | .next _ q =>
      let ⟨_,p',r'⟩ := r.pull q
      ⟨_, .next a p', .keep a r'⟩
  | .seq r s =>
    let ⟨_,q,s'⟩ := s.pull p
    let ⟨_,p',r'⟩ := r.pull q
    ⟨_,p',.seq r' s'⟩

theorem perm {xs ys : List X} (r : AddressOrder X xs ys) : xs.Perm ys := by
  induction r with
  | ident _ => exact List.Perm.refl _
  | swap a b xs => exact .swap b a xs
  | keep a _ ih => exact .cons a ih
  | seq _ _ ih jh => exact ih.trans jh

end AddressOrder
end ContextualComposition.NativeFinitePush.DependentFibre

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
section Braided
variable [BraidedCategory C]

private def pad3 (a b c a' b' c' z : C) (f : a ⊗ (b ⊗ c) ⟶ a' ⊗ (b' ⊗ c')) :
    a ⊗ (b ⊗ (c ⊗ z)) ⟶ a' ⊗ (b' ⊗ (c' ⊗ z)) :=
  (a ◁ (α_ b c z).inv) ≫ (α_ a (b ⊗ c) z).inv ≫ f ▷ z ≫
    (α_ a' (b' ⊗ c') z).hom ≫ a' ◁ (α_ b' c' z).hom

omit [BraidedCategory C] in
private theorem pad3_comp (a b c d e f g h i z : C)
    (p : a ⊗ (b ⊗ c) ⟶ d ⊗ (e ⊗ f)) (q : d ⊗ (e ⊗ f) ⟶ g ⊗ (h ⊗ i)) :
    pad3 a b c d e f z p ≫ pad3 d e f g h i z q = pad3 a b c g h i z (p ≫ q) := by
  unfold pad3
  monoidal

private theorem pad3_left (a b c z : C) :
    pad3 a b c b a c z (crossHead a b c) = crossHead a b (c ⊗ z) := by
  unfold pad3 crossHead
  monoidal

private theorem pad3_right (a b c z : C) :
    pad3 a b c a c b z (a ◁ (β_ b c).hom) = a ◁ crossHead b c z := by
  unfold pad3 crossHead
  monoidal

/-- The adjacent exchange square only needs braiding. Involutivity below
will require symmetry. -/
theorem adjacent_yang_baxter (a b c z : C) :
    crossHead a b (c ⊗ z) ≫ (b ◁ crossHead a c z) ≫ crossHead b c (a ⊗ z) =
      (a ◁ crossHead b c z) ≫ crossHead a c (b ⊗ z) ≫ c ◁ crossHead a b z := by
  rw [← pad3_left a b c z, ← pad3_right b a c z, ← pad3_left b c a z,
      ← pad3_right a b c z, ← pad3_left a c b z, ← pad3_right c a b z]
  simp only [pad3_comp]
  congr 1
  simpa only [crossHead, Category.assoc] using yang_baxter a b c

end Braided

variable [SymmetricCategory C] in
theorem adjacent_involutive (a b z : C) :
    crossHead a b z ≫ crossHead b a z = 𝟙 (a ⊗ (b ⊗ z)) := by
  unfold crossHead
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding b a]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp]


section Normalization
variable [SymmetricCategory C]
variable {X : Type w} (A : X → C)
local notation "𝔉" => fold (binary (Additive.sum (Additive.ofBraided (C:=C)))) (𝟙_ C) A
local notation "route" => AddressOrder.mapSum (additiveStructure (C:=C)) A
local notation "pick" => fun p => route (Pick.address p)

private theorem movePast_std (a b z : C) :
    movePast (additiveStructure (C:=C)) a b z = crossHead a b z := by
  change (α_ a b z).inv ≫ ((β_ a b).hom ⊗ₘ 𝟙 z) ≫ (α_ b a z).hom = _
  rw [tensorHom_id]
  rfl

private theorem route_swap (a b : X) (ts : List X) :
    route (.swap a b ts) = crossHead (A a) (A b) (𝔉 ts) :=
  movePast_std _ _ _

private theorem pick_next {x y : X} {xs ys : List X} (p : Pick x xs ys) :
    pick (.next y p) = (A y ◁ pick p) ≫ crossHead (A y) (A x) (𝔉 ys) := by
  simp only [Pick.address, AddressOrder.mapSum]
  change (𝟙 (A y) ⊗ₘ pick p) ≫ movePast additiveStructure (A y) (A x) (𝔉 ys) = _
  rw [id_tensorHom, movePast_std]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem pull_square {x : X} {xs ys ys' : List X} (r : AddressOrder X xs ys) (p : Pick x ys ys') :
    route r ≫ pick p = pick (r.pull p).2.1 ≫ A x ◁ route (r.pull p).2.2 := by
  induction r generalizing ys' with
  | ident xs =>
    change 𝟙 _ ≫ pick p = pick p ≫ A x ◁ 𝟙 _
    simp only [Category.id_comp, whiskerLeft_id]
    exact (Category.comp_id _).symm
  | swap a b ts =>
    rw [route_swap]
    cases p with
    | here =>
      change crossHead (A a) (A x) (𝔉 ts) ≫ 𝟙 _ = pick (.next a (.here ts)) ≫ A x ◁ 𝟙 _
      rw [pick_next]
      change _ = ((A a ◁ 𝟙 _) ≫ _) ≫ A x ◁ 𝟙 _
      simp only [Category.id_comp, whiskerLeft_id, Category.comp_id]
    | next b q =>
      cases q with
      | here =>
        change crossHead (A x) (A b) (𝔉 ts) ≫ pick (.next b (.here ts)) = 𝟙 _ ≫ A x ◁ 𝟙 _
        rw [pick_next]
        change _ ≫ ((A b ◁ 𝟙 _) ≫ _) = _
        simp only [Category.id_comp, whiskerLeft_id]
        exact adjacent_involutive _ _ _
      | @next a ts zs q =>
        change crossHead (A a) (A b) (𝔉 ts) ≫ pick (.next b (.next a q)) =
          pick (.next a (.next b q)) ≫ A x ◁ route (.swap a b zs)
        rw [route_swap]
        simp only [pick_next, whiskerLeft_comp, Category.assoc, fold]
        rw [← Category.assoc (crossHead _ _ _) (A b ◁ A a ◁ pick q), crossHead_nat, Category.assoc]
        exact congrArg (fun f => (A a ◁ A b ◁ pick q) ≫ f)
          (adjacent_yang_baxter (A a) (A b) (A x) (𝔉 zs))
  | keep a r ih =>
    cases p with
    | here =>
      change (𝟙 _ ⊗ₘ route r) ≫ 𝟙 _ = 𝟙 _ ≫ A x ◁ route r
      simp only [id_tensorHom, Category.id_comp, Category.comp_id]
    | @next _ _ zs q =>
      have eq := ih q
      change ((𝟙 _ ⊗ₘ route r) ≫ pick (.next a q)) =
        pick (.next a (r.pull q).2.1) ≫ A x ◁ (𝟙 _ ⊗ₘ route (r.pull q).2.2)
      rw [pick_next, pick_next]
      simp only [id_tensorHom, fold]
      rw [← whiskerLeft_comp_assoc, eq, whiskerLeft_comp, Category.assoc]
      rw [Category.assoc, crossHead_nat]
  | seq r s hr hs =>
    change ((route r ≫ route s) ≫ pick p) =
      pick (r.pull (s.pull p).2.1).2.1 ≫
        A x ◁ (route (r.pull (s.pull p).2.1).2.2 ≫ route (s.pull p).2.2)
    rw [Category.assoc, hs p, ← Category.assoc, hr (s.pull p).2.1, Category.assoc, whiskerLeft_comp]


private theorem route_empty {xs ys : List X} (r : AddressOrder X xs ys)
    (h : xs = []) (g : ys = []) : HEq (route r) (𝟙 (𝟙_ C)) := by
  induction r with
  | ident z => subst z; rfl
  | swap => contradiction
  | keep => contradiction
  | @seq a b c r s hr hs =>
    have e : b = [] := (List.Perm.nil_eq (h ▸ r.perm)).symm
    subst a
    subst b
    subst c
    change HEq (route r ≫ route s) (𝟙 (𝟙_ C))
    rw [eq_of_heq (hr rfl rfl), eq_of_heq (hs rfl rfl)]
    exact heq_of_eq (Category.id_comp _)

/-- All typed adjacent-swap programs between the same pair of distinct-tag
words have the same interpretation in a symmetric monoidal category.
Only the addresses must be distinct. Coefficients can agree arbitrarily. -/
theorem tagged_permutation_coherent {xs ys : List X} (hn : xs.Nodup)
    (r s : AddressOrder X xs ys) : route r = route s := by
  induction ys generalizing xs with
  | nil =>
    have e := (List.Perm.nil_eq r.perm.symm).symm
    exact eq_of_heq ((route_empty A r e rfl).trans (route_empty A s e rfl).symm)
  | cons y ys ih =>
    let p : Pick y (y::ys) ys := .here ys
    have hr := pull_square A r p
    have hs := pull_square A s p
    have H := Pick.unique hn
      (⟨(r.pull p).1, (r.pull p).2.1⟩ : Σ zs, Pick y xs zs)
      ⟨(s.pull p).1, (s.pull p).2.1⟩
    rcases e₁ : r.pull p with ⟨rs, rp, rr⟩
    rcases e₂ : s.pull p with ⟨ss, sp, sr⟩
    rw [e₁, e₂] at H
    have eq := congrArg Sigma.fst H
    dsimp at eq
    subst ss
    have eqP : rp = sp := eq_of_heq (Sigma.mk.inj H).2
    subst sp
    have h₁ : ys.Nodup := (List.nodup_cons.mp (r.perm.nodup_iff.mp hn)).2
    have h₂ : rs.Nodup := rr.perm.nodup_iff.mpr h₁
    have E := ih h₂ rr sr
    rw [e₁] at hr
    rw [e₂] at hs
    change _ ≫ 𝟙 _ = _ at hr hs
    simp only [Category.comp_id] at hr hs
    exact hr.trans ((congrArg (fun f => pick rp ≫ A y ◁ f) E).trans hs.symm)

end Normalization
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
