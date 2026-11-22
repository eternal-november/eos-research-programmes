module
public import ContextualComposition.StandardDirectImage
@[expose] public section

namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory BraidedCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C
variable {X : Type w} (A : X → C)

def taggedTail (xs : List X) (z : C) := tailFold (xs.map A) z
local notation "F" => taggedTail A

def taggedTailMap {xs ys : List X} (r : AddressOrder X xs ys) (z : C) :
    F xs z ⟶ F ys z :=
  match r with
  | .ident _ => 𝟙 _
  | .swap a b xs => crossHead (A a) (A b) (F xs z)
  | .keep a p => A a ◁ taggedTailMap p z
  | .seq p q => taggedTailMap p z ≫ taggedTailMap q z

def taggedExtract (a : X) (xs ys : List X) : AddressOrder X (xs ++ a::ys) (a::(xs ++ ys)) :=
  match xs with
  | [] => .ident _
  | b::bs => .seq (.keep b (taggedExtract a bs ys)) (.swap b a _)

def taggedBlockSwap (xs ys ts : List X) :
    AddressOrder X (xs ++ (ys ++ ts)) (ys ++ (xs ++ ts)) :=
  match ys with
  | [] => .ident _
  | b::bs => .seq (taggedExtract b xs (bs ++ ts)) (.keep b (taggedBlockSwap xs bs ts))

omit [SymmetricCategory C] in
theorem tailAppend (xs ys : List X) (z : C) : F xs (F ys z) = F (xs ++ ys) z := by
  unfold taggedTail
  rw [List.map_append]
  exact tail_append_obj _ _ _

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory C] in
theorem tailAppend_cons_iso (x : X) (xs ys : List X) (z : C) :
    eqToHom (tailAppend A (x::xs) ys z) = A x ◁ eqToHom (tailAppend A xs ys z) := by
  rw [whiskerLeft_eqToHom]

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory C] in
theorem tailAppend_cons_iso_inv (x : X) (xs ys : List X) (z : C) :
    eqToHom (tailAppend A (x::xs) ys z).symm = A x ◁ eqToHom (tailAppend A xs ys z).symm := by
  rw [whiskerLeft_eqToHom]

set_option backward.isDefEq.respectTransparency false in
theorem taggedExtract_correct (a : X) (xs ys : List X) (z : C) :
    eqToHom (tailAppend A xs (a::ys) z) ≫ taggedTailMap A (taggedExtract a xs ys) z ≫
      A a ◁ eqToHom (tailAppend A xs ys z).symm =
        extract (A a) (xs.map A) (F ys z) := by
  induction xs with
  | nil =>
    change 𝟙 _ ≫ 𝟙 _ ≫ A a ◁ 𝟙 _ = 𝟙 _
    simp only [Category.id_comp, whiskerLeft_id]
  | cons b bs ih =>
    rw [tailAppend_cons_iso, tailAppend_cons_iso_inv]
    change (A b ◁ eqToHom (tailAppend A bs (a::ys) z)) ≫
      ((A b ◁ taggedTailMap A (taggedExtract a bs ys) z) ≫ crossHead (A b) (A a) (F (bs ++ ys) z)) ≫
      A a ◁ A b ◁ eqToHom (tailAppend A bs ys z).symm =
      (A b ◁ extract (A a) (bs.map A) (F ys z)) ≫ crossHead (A b) (A a) (F bs (F ys z))
    simp only [Category.assoc]
    rw [crossHead_nat, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc, ih]


omit [SymmetricCategory C] in
theorem tailTriple (xs ys ts : List X) (z : C) :
    F xs (F ys (F ts z)) = F (xs ++ (ys ++ ts)) z :=
  (congrArg (F xs) (tailAppend A ys ts z)).trans (tailAppend A xs (ys ++ ts) z)

theorem extract_natural (a : C) (xs : List C) {t u' : C} (f : t ⟶ u') :
    extract a xs t ≫ (a ◁ tailMap xs f) =
      tailMap xs (a ◁ f) ≫ extract a xs u' := by
  -- Only the braiding is used in this naturality square.
  induction xs with
  | nil =>
    change 𝟙 _ ≫ a ◁ f = a ◁ f ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | cons b xs ih =>
    change ((b ◁ extract a xs t) ≫ crossHead b a (tailFold xs t)) ≫ a ◁ b ◁ tailMap xs f =
      (b ◁ tailMap xs (a ◁ f)) ≫ (b ◁ extract a xs u') ≫ crossHead b a (tailFold xs u')
    rw [Category.assoc, crossHead_nat, ← whiskerLeft_comp_assoc, ih, whiskerLeft_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem taggedExtract_segment (a : X) (xs ys ts : List X) (z : C) :
    eqToHom (tailTriple A xs (a::ys) ts z) ≫ taggedTailMap A (taggedExtract a xs (ys ++ ts)) z ≫
      A a ◁ eqToHom (tailTriple A xs ys ts z).symm =
        extract (A a) (xs.map A) (F ys (F ts z)) := by
  let e := tailAppend A ys ts z
  let f := eqToHom e
  let fi := eqToHom e.symm
  let fc := tailMap (xs.map A) fi
  let fa := tailMap (xs.map A) (A a ◁ f)
  let T := taggedTailMap A (taggedExtract a xs (ys ++ ts)) z
  have inL : eqToHom (tailTriple A xs (a::ys) ts z) = fa ≫
      eqToHom (tailAppend A xs (a::(ys ++ ts)) z) := by
    unfold fa f e
    rw [← tailAppend_cons_iso, tailMap_eqToHom, eqToHom_trans]
  have inR : eqToHom (tailTriple A xs ys ts z).symm =
      eqToHom (tailAppend A xs (ys ++ ts) z).symm ≫ fc := by
    unfold fc fi
    rw [tailMap_eqToHom, eqToHom_trans]
  have H := taggedExtract_correct A a xs (ys ++ ts) z
  change _ ≫ T ≫ _ = _ at H
  rw [inL, inR, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom (tailAppend A xs (a::(ys ++ ts)) z)) T,
    ← Category.assoc ((eqToHom (tailAppend A xs (a::(ys ++ ts)) z)) ≫ T),
    Category.assoc (eqToHom (tailAppend A xs (a::(ys ++ ts)) z)) T, H]
  have n := extract_natural (A a) (xs.map A) f
  change extract (A a) (xs.map A) (F ys (F ts z)) ≫
    A a ◁ tailMap (xs.map A) f = fa ≫ extract (A a) (xs.map A) (F (ys ++ ts) z) at n
  rw [← Category.assoc fa, ← n, Category.assoc, ← whiskerLeft_comp]
  have h : tailMap (xs.map A) f ≫ fc = 𝟙 (F xs (F ys (F ts z))) := by
    unfold fc f fi
    rw [tailMap_eqToHom, tailMap_eqToHom, eqToHom_trans]
    rfl
  rw [h]
  let E : F xs (A a ⊗ F ys (F ts z)) ⟶ A a ⊗ F xs (F ys (F ts z)) :=
    extract (A a) (xs.map A) (F ys (F ts z))
  change E ≫ A a ◁ 𝟙 (F xs (F ys (F ts z))) = E
  rw [whiskerLeft_id, Category.comp_id]


set_option backward.isDefEq.respectTransparency false in
theorem taggedBlockSwap_correct (xs ys ts : List X) (z : C) :
    eqToHom (tailTriple A xs ys ts z) ≫ taggedTailMap A (taggedBlockSwap xs ys ts) z ≫
      eqToHom (tailTriple A ys xs ts z).symm =
        swapBlocks (xs.map A) (ys.map A) (F ts z) := by
  induction ys with
  | nil =>
    change eqToHom (tailAppend A xs ts z) ≫ 𝟙 _ ≫ eqToHom (tailAppend A xs ts z).symm = 𝟙 _
    rw [Category.id_comp, eqToHom_trans]
    rfl
  | cons b bs ih =>
    have right : eqToHom (tailTriple A (b::bs) xs ts z).symm =
        A b ◁ eqToHom (tailTriple A bs xs ts z).symm := by
      rw [whiskerLeft_eqToHom]
    let p := taggedTailMap A (taggedExtract b xs (bs ++ ts)) z
    let q := taggedTailMap A (taggedBlockSwap xs bs ts) z
    let j := eqToHom (tailTriple A xs bs ts z)
    let j' := eqToHom (tailTriple A xs bs ts z).symm
    let k := eqToHom (tailTriple A bs xs ts z).symm
    let i := eqToHom (tailTriple A xs (b::bs) ts z)
    let U := swapBlocks (xs.map A) (bs.map A) (F ts z)
    let E := extract (A b) (xs.map A) (F bs (F ts z))
    rw [right]
    change i ≫ (p ≫ A b ◁ q) ≫ A b ◁ k = E ≫ A b ◁ U
    have e : i ≫ p ≫ A b ◁ j' = E := taggedExtract_segment A b xs bs ts z
    have jinv : j' ≫ j = 𝟙 (F (xs ++ (bs ++ ts)) z) := by
      unfold j' j
      rw [eqToHom_trans]
      rfl
    have ih' : j ≫ q ≫ k = U := ih
    calc
      _ = (i ≫ p ≫ A b ◁ j') ≫ (A b ◁ (j ≫ q ≫ k)) := by
        simp only [Category.assoc, ← whiskerLeft_comp]
        rw [← Category.assoc j', jinv, Category.id_comp]
      _ = _ := by rw [e, ih']


local notation "G" => fold 𝒮 Z A

theorem fold_eq_taggedTail (xs : List X) : G xs = F xs Z := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (fun c => A a ⊗ c) ih

def toTail (xs : List X) : G xs ⟶ F xs Z := eqToHom (fold_eq_taggedTail A xs)

set_option backward.isDefEq.respectTransparency false in
theorem toTail_cons (a : X) (xs : List X) : toTail A (a::xs) = A a ◁ toTail A xs := by
  unfold toTail
  rw [whiskerLeft_eqToHom]

set_option backward.isDefEq.respectTransparency false in
theorem taggedTailMap_bridge {xs ys : List X} (r : AddressOrder X xs ys) :
    AddressOrder.mapSum additiveStructure A r ≫ toTail A ys =
      toTail A xs ≫ taggedTailMap A r Z := by
  induction r with
  | ident xs =>
    change 𝟙 (G xs) ≫ toTail A xs = toTail A xs ≫ 𝟙 (F xs Z)
    rw [Category.id_comp, Category.comp_id]
  | swap a b xs =>
    rw [toTail_cons, toTail_cons, toTail_cons, toTail_cons]
    change ((α_ (A a) (A b) (G xs)).inv ≫ ((β_ (A a) (A b)).hom ⊗ₘ 𝟙 (G xs)) ≫
      (α_ (A b) (A a) (G xs)).hom) ≫ A b ◁ A a ◁ toTail A xs =
      (A a ◁ A b ◁ toTail A xs) ≫ crossHead (A a) (A b) (F xs Z)
    rw [tensorHom_id]
    exact crossHead_nat _ _ _
  | keep a r ih =>
    rw [toTail_cons, toTail_cons]
    change (𝟙 (A a) ⊗ₘ AddressOrder.mapSum additiveStructure A r) ≫ A a ◁ toTail A _ =
      (A a ◁ toTail A _) ≫ A a ◁ taggedTailMap A r Z
    rw [id_tensorHom, ← whiskerLeft_comp, ← whiskerLeft_comp, ih]
  | seq r s hr hs =>
    change (AddressOrder.mapSum additiveStructure A r ≫ AddressOrder.mapSum additiveStructure A s) ≫
      toTail A _ = toTail A _ ≫ (taggedTailMap A r Z ≫ taggedTailMap A s Z)
    rw [Category.assoc, hs, ← Category.assoc, hr, Category.assoc]

def tailJoin (xs ys : List X) : F (xs ++ ys) Z ⟶ F xs Z ⊗ F ys Z :=
  eqToHom (tailAppend A xs ys Z).symm ≫ splitTail (xs.map A) (F ys Z)

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory C] in
theorem tailJoin_cons (a : X) (xs ys : List X) :
    tailJoin A (a::xs) ys = (A a ◁ tailJoin A xs ys) ≫ (α_ (A a) (F xs Z) (F ys Z)).inv := by
  unfold tailJoin
  rw [tailAppend_cons_iso_inv]
  change (A a ◁ eqToHom (tailAppend A xs ys Z).symm) ≫
    (A a ◁ splitTail (xs.map A) (F ys Z)) ≫ (α_ (A a) (F xs Z) (F ys Z)).inv = _
  rw [← whiskerLeft_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem tailJoin_bridge (xs ys : List X) :
    toTail A (xs ++ ys) ≫ tailJoin A xs ys =
      join additiveStructure A xs ys ≫ (toTail A xs ⊗ₘ toTail A ys) := by
  induction xs with
  | nil =>
    change toTail A ys ≫ (𝟙 _ ≫ (λ_ (F ys Z)).inv) =
      (λ_ (G ys)).inv ≫ (𝟙 Z ⊗ₘ toTail A ys)
    rw [Category.id_comp, id_tensorHom, leftUnitor_inv_naturality]
  | cons a xs ih =>
    simp only [List.cons_append, toTail_cons, tailJoin_cons, std_join_cons]
    let J : G (xs ++ ys) ⟶ G xs ⊗ G ys := join additiveStructure A xs ys
    change (A a ◁ toTail A (xs ++ ys)) ≫ (A a ◁ tailJoin A xs ys) ≫
        (α_ (A a) (F xs Z) (F ys Z)).inv =
      ((A a ◁ J) ≫ (α_ (A a) (G xs) (G ys)).inv) ≫ ((A a ◁ toTail A xs) ⊗ₘ toTail A ys)
    rw [← whiskerLeft_comp_assoc, ih, whiskerLeft_comp, Category.assoc, Category.assoc]
    have h := associator_inv_naturality (𝟙 (A a)) (toTail A xs) (toTail A ys)
    simpa only [id_tensorHom] using congrArg (fun f => (A a ◁ J) ≫ f) h


def packBlocks (xs ys ts : List X) : G (xs ++ (ys ++ ts)) ⟶ (G xs ⊗ G ys) ⊗ G ts :=
  join additiveStructure A xs (ys ++ ts) ≫
    (G xs ◁ join additiveStructure A ys ts) ≫ (α_ (G xs) (G ys) (G ts)).inv

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory C] in
theorem tailSeparate_eq (xs ys ts : List X) :
    eqToHom (tailTriple A xs ys ts Z).symm ≫ separateBlocks (xs.map A) (ys.map A) (F ts Z) =
      tailJoin A xs (ys ++ ts) ≫ F xs Z ◁ tailJoin A ys ts ≫ (α_ (F xs Z) (F ys Z) (F ts Z)).inv := by
  let e := tailAppend A ys ts Z
  let d := tailAppend A xs (ys ++ ts) Z
  have a : eqToHom (tailTriple A xs ys ts Z).symm =
      eqToHom d.symm ≫ tailMap (xs.map A) (eqToHom e.symm) := by
    rw [tailMap_eqToHom, eqToHom_trans]
  rw [a]
  unfold separateBlocks tailJoin
  simp only [Category.assoc, whiskerLeft_comp]
  let f : F (ys ++ ts) Z ⟶ F ys (F ts Z) := eqToHom e.symm
  have h : tailMap (xs.map A) f ≫ splitTail (xs.map A) (F ys (F ts Z)) =
      splitTail (xs.map A) (F (ys ++ ts) Z) ≫ F xs Z ◁ f :=
    splitTail_map (xs.map A) f
  rw [← Category.assoc (tailMap (xs.map A) _)]
  have H := congrArg (fun m => eqToHom d.symm ≫ m ≫
      (F xs Z ◁ splitTail (ys.map A) (F ts Z)) ≫ (α_ (F xs Z) (F ys Z) (F ts Z)).inv) h
  simp only [Category.assoc] at H ⊢
  exact H

set_option backward.isDefEq.respectTransparency false in
theorem packBlocks_bridge (xs ys ts : List X) :
    toTail A (xs ++ (ys ++ ts)) ≫ eqToHom (tailTriple A xs ys ts Z).symm ≫
      separateBlocks (xs.map A) (ys.map A) (F ts Z) =
        packBlocks A xs ys ts ≫ ((toTail A xs ⊗ₘ toTail A ys) ⊗ₘ toTail A ts) := by
  rw [tailSeparate_eq, ← Category.assoc, tailJoin_bridge]
  unfold packBlocks
  simp only [Category.assoc]
  let J : G (ys ++ ts) ⟶ G ys ⊗ G ts := join additiveStructure A ys ts
  let T := tailJoin A ys ts
  let p := toTail A xs
  let q := toTail A (ys ++ ts)
  let r := toTail A ys
  let s := toTail A ts
  have h : (p ⊗ₘ q) ≫ F xs Z ◁ T = (G xs ◁ J) ≫ (p ⊗ₘ (r ⊗ₘ s)) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg (fun u => p ⊗ₘ u) (tailJoin_bridge A ys ts)
  have k := associator_inv_naturality p r s
  change _ ≫ ((p ⊗ₘ q) ≫ (F xs Z ◁ T) ≫ _) =
      _ ≫ ((G xs ◁ J) ≫ (α_ (G xs) (G ys) (G ts)).inv ≫ ((p ⊗ₘ r) ⊗ₘ s))
  rw [reassoc_of% h]
  exact congrArg (fun m => join additiveStructure A xs (ys ++ ts) ≫ G xs ◁ J ≫ m) k


instance toTail_iso (xs : List X) : IsIso (toTail A xs) := by
  unfold toTail
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem swap_pack_blocks (xs ys ts : List X) :
    AddressOrder.mapSum additiveStructure A (taggedBlockSwap xs ys ts) ≫ packBlocks A ys xs ts =
      packBlocks A xs ys ts ≫ (β_ (G xs) (G ys)).hom ▷ G ts := by
  let r := taggedBlockSwap xs ys ts
  let input := xs ++ (ys ++ ts)
  let output := ys ++ (xs ++ ts)
  let a := eqToHom (tailTriple A xs ys ts Z).symm
  let b := eqToHom (tailTriple A ys xs ts Z).symm
  let d := eqToHom (tailTriple A xs ys ts Z)
  let p := (toTail A xs ⊗ₘ toTail A ys) ⊗ₘ toTail A ts
  let q := (toTail A ys ⊗ₘ toTail A xs) ⊗ₘ toTail A ts
  let k := (β_ (G xs) (G ys)).hom ▷ G ts
  let l := (β_ (F xs Z) (F ys Z)).hom ▷ F ts Z
  let J₁ := packBlocks A xs ys ts
  let J₂ := packBlocks A ys xs ts
  let S₁ := separateBlocks (xs.map A) (ys.map A) (F ts Z)
  let S₂ := separateBlocks (ys.map A) (xs.map A) (F ts Z)
  let W := swapBlocks (xs.map A) (ys.map A) (F ts Z)
  let m := AddressOrder.mapSum additiveStructure A r
  let n := taggedTailMap A r Z
  have h₁ : toTail A input ≫ a ≫ S₁ = J₁ ≫ p := packBlocks_bridge A xs ys ts
  have h₂ : toTail A output ≫ b ≫ S₂ = J₂ ≫ q := packBlocks_bridge A ys xs ts
  have h₃ : d ≫ n ≫ b = W := taggedBlockSwap_correct A xs ys ts Z
  have h₄ : W ≫ S₂ = S₁ ≫ l := swapBlocks_grouped (xs.map A) (ys.map A) (F ts Z)
  have h₅ : m ≫ toTail A output = toTail A input ≫ n := taggedTailMap_bridge A r
  have h₆ : k ≫ q = p ≫ l := by
    unfold k l p q
    rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, braiding_naturality]
  have h₇ : a ≫ d = 𝟙 _ := by
    unfold a d
    rw [eqToHom_trans]
    rfl
  let _ : IsIso q := by unfold q; infer_instance
  change m ≫ J₂ = J₁ ≫ k
  apply (cancel_mono q).mp
  calc
    (m ≫ J₂) ≫ q = (m ≫ toTail A output) ≫ b ≫ S₂ := by
      simp only [Category.assoc, ← h₂]
    _ = toTail A input ≫ a ≫ (d ≫ n ≫ b) ≫ S₂ := by
      rw [h₅]
      simp only [Category.assoc, reassoc_of% h₇]
    _ = (J₁ ≫ p) ≫ l := by
      rw [h₃]
      have h := congrArg (fun t => toTail A input ≫ a ≫ t) h₄
      have g := congrArg (fun t => t ≫ l) h₁
      simp only [Category.assoc] at g ⊢
      exact h.trans g
    _ = (J₁ ≫ k) ≫ q := by rw [Category.assoc, Category.assoc, h₆]


variable {Y : Type*} (L : Y → List X)
def liftRows {ys ys' : List Y} (r : AddressOrder Y ys ys') :
    AddressOrder X (ys.flatMap L) (ys'.flatMap L) :=
  match r with
  | .ident _ => .ident _
  | .swap a b ys => taggedBlockSwap (L a) (L b) (ys.flatMap L)
  | .keep a p => AddressOrder.prepend (L a) (liftRows p)
  | .seq p q => .seq (liftRows p) (liftRows q)

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_two (a b : Y) (ys : List Y) :
    rowsChart A L (a::b::ys) = packBlocks A (L a) (L b) (ys.flatMap L) ≫
      (α_ (G (L a)) (G (L b)) (G (ys.flatMap L))).hom ≫
      G (L a) ◁ G (L b) ◁ rowsChart A L ys := by
  let P : G (L b ++ ys.flatMap L) ⟶ G (L b) ⊗ G (ys.flatMap L) :=
    join additiveStructure A (L b) (ys.flatMap L)
  let Q : G (L a ++ (L b ++ ys.flatMap L)) ⟶ G (L a) ⊗ G (L b ++ ys.flatMap L) :=
    join additiveStructure A (L a) (L b ++ ys.flatMap L)
  let f := rowsChart A L ys
  change Q ≫ (𝟙 (G (L a)) ⊗ₘ (P ≫ (𝟙 (G (L b)) ⊗ₘ f))) =
    (Q ≫ G (L a) ◁ P ≫ (α_ _ _ _).inv) ≫ (α_ _ _ _).hom ≫ G (L a) ◁ G (L b) ◁ f
  simp only [id_tensorHom, whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_liftRows {ys ys' : List Y} (r : AddressOrder Y ys ys') :
    AddressOrder.mapSum additiveStructure A (liftRows L r) ≫ rowsChart A L ys' =
      rowsChart A L ys ≫ AddressOrder.mapSum additiveStructure (fun y => G (L y)) r := by
  induction r with
  | ident ys =>
    change 𝟙 _ ≫ rowsChart A L ys = rowsChart A L ys ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | swap a b ys =>
    rw [rowsChart_two, rowsChart_two]
    change AddressOrder.mapSum additiveStructure A (taggedBlockSwap (L a) (L b) (ys.flatMap L)) ≫
        (packBlocks A (L b) (L a) (ys.flatMap L) ≫
          (α_ _ _ _).hom ≫ G (L b) ◁ G (L a) ◁ rowsChart A L ys) =
      (packBlocks A (L a) (L b) (ys.flatMap L) ≫ (α_ _ _ _).hom ≫
        G (L a) ◁ G (L b) ◁ rowsChart A L ys) ≫
        movePast additiveStructure (G (L a)) (G (L b)) _
    rw [reassoc_of% (swap_pack_blocks A (L a) (L b) (ys.flatMap L))]
    have h : movePast additiveStructure (G (L a)) (G (L b))
        (fold 𝒮 Z (fun y => G (L y)) ys) =
      crossHead (G (L a)) (G (L b)) (fold 𝒮 Z (fun y => G (L y)) ys) := by
      change (α_ _ _ _).inv ≫ ((β_ _ _).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom = _
      rw [tensorHom_id]
      rfl
    rw [h]
    let p := packBlocks A (L a) (L b) (ys.flatMap L)
    let U := G (L a)
    let V := G (L b)
    let f := rowsChart A L ys
    have m := crossHead_nat U V f
    calc
      _ = p ≫ (α_ U V _).hom ≫
          (crossHead U V _ ≫ V ◁ U ◁ f) := by
        unfold crossHead
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rfl
      _ = _ := by rw [m]; simp only [Category.assoc]; rfl
  | keep a r ih =>
    change AddressOrder.mapSum additiveStructure A (AddressOrder.prepend (L a) (liftRows L r)) ≫
        (join additiveStructure A (L a) _ ≫ (𝟙 (G (L a)) ⊗ₘ rowsChart A L _)) =
      (join additiveStructure A (L a) _ ≫ (𝟙 (G (L a)) ⊗ₘ rowsChart A L _)) ≫
        (𝟙 (G (L a)) ⊗ₘ AddressOrder.mapSum additiveStructure (fun y => G (L y)) r)
    rw [← Category.assoc, std_join_prefix, Category.assoc, Category.assoc, id_tensorHom, id_tensorHom,
      id_tensorHom, ← whiskerLeft_comp, ← whiskerLeft_comp, ih]
  | seq p q hp hq =>
    change (AddressOrder.mapSum additiveStructure A (liftRows L p) ≫
      AddressOrder.mapSum additiveStructure A (liftRows L q)) ≫ rowsChart A L _ =
      rowsChart A L _ ≫ (AddressOrder.mapSum additiveStructure (fun y => G (L y)) p ≫
        AddressOrder.mapSum additiveStructure (fun y => G (L y)) q)
    rw [Category.assoc, hq, ← Category.assoc, hp, Category.assoc]

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
