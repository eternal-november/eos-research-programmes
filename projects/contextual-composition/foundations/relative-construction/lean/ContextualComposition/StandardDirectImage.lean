module
public import ContextualComposition.TaggedChart

@[expose] public section
/-! Standard symmetric additive finite direct image: the carrier map is
arbitrary, fibres are ordered address lists, and each coefficient sum
contains actual summands and its explicit nullary terminal. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w w'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Z" => 𝟙_ C

variable {X : Type w} {Y : Type w'} (A : X → C) (L : Y → List X)
/-- Convert a flat word ordered by rows into the actual iterate of sums. -/
def rowsChart : (ys : List Y) → fold 𝒮 Z A (ys.flatMap L) ⟶
    fold 𝒮 Z (fun y => fold 𝒮 Z A (L y)) ys
  | [] => 𝟙 _
  | y::ys => join additiveStructure A (L y) (ys.flatMap L) ≫
      (𝟙 (fold 𝒮 Z A (L y)) ⊗ₘ rowsChart ys)

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_natural {A B : X → C} (p : ∀ x, A x ⟶ B x) (ys : List Y) :
    act 𝒮 Z p (ys.flatMap L) ≫ rowsChart B L ys =
      rowsChart A L ys ≫ act 𝒮 Z (fun y => act 𝒮 Z p (L y)) ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have e : act 𝒮 Z p (L y ++ ys.flatMap L) ≫ join additiveStructure B (L y) (ys.flatMap L) =
        join additiveStructure A (L y) (ys.flatMap L) ≫
          (act 𝒮 Z p (L y) ⊗ₘ act 𝒮 Z p (ys.flatMap L)) :=
      act_append additiveNaturality p (L y) (ys.flatMap L)
    change act 𝒮 Z p (L y ++ ys.flatMap L) ≫
      (join additiveStructure B (L y) (ys.flatMap L) ≫ (𝟙 _ ⊗ₘ rowsChart B L ys)) =
        (join additiveStructure A (L y) (ys.flatMap L) ≫ (𝟙 _ ⊗ₘ rowsChart A L ys)) ≫
          (act 𝒮 Z p (L y) ⊗ₘ act 𝒮 Z (fun y => act 𝒮 Z p (L y)) ys)
    rw [← Category.assoc, e, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, ih]

theorem fibreList_nodup {n m : Nat} (f : Fin n → Fin m) (j : Fin m) :
    (fibreList f j).Nodup :=
  (List.nodup_finRange _).filter _

theorem rowPartition_nodup {n m : Nat} (f : Fin n → Fin m) (ys : List (Fin m))
    (hn : ys.Nodup) : (ys.flatMap (fibreList f)).Nodup := by
  induction ys with
  | nil => exact List.nodup_nil
  | cons y ys ih =>
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨fibreList_nodup f y, ih (List.nodup_cons.mp hn).2, ?_⟩
    intro x hx _ hxy e
    subst e
    obtain ⟨z, hz, hzx⟩ := List.mem_flatMap.mp hxy
    have h := (mem_fibreList.mp hx).symm.trans (mem_fibreList.mp hzx)
    exact (List.nodup_cons.mp hn).1 (h ▸ hz)

theorem rowPartition_perm {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l) (j : Fin l) :
    (fibreList (g ∘ f) j).Perm ((fibreList g j).flatMap (fibreList f)) := by
  apply (List.perm_ext_iff_of_nodup (fibreList_nodup _ _)
    (rowPartition_nodup f _ (fibreList_nodup _ _))).mpr
  intro x
  simp only [mem_fibreList, List.mem_flatMap, Function.comp_apply]
  exact ⟨fun h => ⟨f x,h,rfl⟩, by rintro ⟨y,h,rfl⟩; exact h⟩

def standardPushObj {n m : Nat} (f : Fin n → Fin m) (A : Fin n → C) (j : Fin m) : C :=
  fold 𝒮 Z A (fibreList f j)

def standardPushMap {n m : Nat} (f : Fin n → Fin m) {A B : Fin n → C}
    (p : ∀ i, A i ⟶ B i) (j : Fin m) :
    standardPushObj f A j ⟶ standardPushObj f B j :=
  act 𝒮 Z p (fibreList f j)

theorem standardPushMap_id {n m : Nat} (f : Fin n → Fin m) (A : Fin n → C) (j : Fin m) :
    standardPushMap f (fun x => 𝟙 (A x)) j = 𝟙 (standardPushObj f A j) :=
  occurrence_act_id A (fibreList f j)

theorem standardPushMap_comp {n m : Nat} (f : Fin n → Fin m) {A B D : Fin n → C}
    (p : ∀ x, A x ⟶ B x) (q : ∀ x, B x ⟶ D x) (j : Fin m) :
    standardPushMap f (fun x => p x ≫ q x) j =
      standardPushMap f p j ≫ standardPushMap f q j :=
  (act_seq 𝒮 Z p q (fibreList f j)).symm

/-- A chosen circuit exists for the actual ordered flat fibre and its
partition into ordered non-injective fibres. -/
noncomputable def splitOrder {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l) (j : Fin l) :
    AddressOrder (Fin n) (fibreList (g ∘ f) j) ((fibreList g j).flatMap (fibreList f)) :=
  Classical.choice (AddressOrder.ofPerm (rowPartition_perm f g j))

noncomputable def standardPushSplit {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    (A : Fin n → C) (j : Fin l) :
    standardPushObj (g ∘ f) A j ⟶ standardPushObj g (standardPushObj f A) j :=
  AddressOrder.mapSum additiveStructure A (splitOrder f g j) ≫
    rowsChart A (fibreList f) (fibreList g j)

theorem standardPushSplit_choice {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    (A : Fin n → C) (j : Fin l)
    (r : AddressOrder (Fin n) (fibreList (g ∘ f) j) ((fibreList g j).flatMap (fibreList f))) :
    standardPushSplit f g A j = AddressOrder.mapSum additiveStructure A r ≫
      rowsChart A (fibreList f) (fibreList g j) :=
  congrArg (fun q => q ≫ rowsChart A (fibreList f) (fibreList g j))
    (tagged_permutation_coherent A (fibreList_nodup _ _) (splitOrder f g j) r)

set_option backward.isDefEq.respectTransparency false in
theorem standardPushSplit_natural {n m l : Nat} (f : Fin n → Fin m) (g : Fin m → Fin l)
    {A B : Fin n → C} (p : ∀ x, A x ⟶ B x) (j : Fin l) :
    standardPushMap (g ∘ f) p j ≫ standardPushSplit f g B j =
      standardPushSplit f g A j ≫ standardPushMap g (standardPushMap f p) j := by
  let r := splitOrder f g j
  have h : standardPushMap (g ∘ f) p j ≫ AddressOrder.mapSum additiveStructure B r =
      AddressOrder.mapSum additiveStructure A r ≫ act 𝒮 Z p _ :=
    AddressOrder.natural additiveNaturality p r
  change _ ≫ (AddressOrder.mapSum additiveStructure B r ≫ _) =
    (AddressOrder.mapSum additiveStructure A r ≫ _) ≫ _
  rw [← Category.assoc, h, Category.assoc, Category.assoc, rowsChart_natural]
  rfl


theorem fibreList_id {n : Nat} (j : Fin n) : fibreList id j = [j] := by
  have h : j ∈ fibreList id j := mem_fibreList.mpr rfl
  rcases e : fibreList id j with _ | ⟨x,xs⟩
  · simp [e] at h
  · have p : x = j := mem_fibreList.mp (e.symm ▸ List.mem_cons_self)
    subst x
    congr 1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    have h' : a = j := mem_fibreList.mp (e.symm ▸ List.mem_cons_of_mem j ha)
    subst a
    exact (List.nodup_cons.mp (e ▸ fibreList_nodup id j)).1 ha

def standardPushSingle {n : Nat} (A : Fin n → C) (j : Fin n) :
    standardPushObj id A j ⟶ A j :=
  eqToHom (congrArg (fold 𝒮 Z A) (fibreList_id j)) ≫ (ρ_ (A j)).hom

set_option backward.isDefEq.respectTransparency false in
theorem standardPushSingle_natural {n : Nat} {A B : Fin n → C}
    (p : ∀ x, A x ⟶ B x) (j : Fin n) :
    standardPushMap id p j ≫ standardPushSingle B j =
      standardPushSingle A j ≫ p j := by
  have aux (ls : List (Fin n)) (e : ls = [j]) :
      act 𝒮 Z p ls ≫ eqToHom (congrArg (fold 𝒮 Z B) e) ≫ (ρ_ (B j)).hom =
        (eqToHom (congrArg (fold 𝒮 Z A) e) ≫ (ρ_ (A j)).hom) ≫ p j := by
    subst ls
    simp only [eqToHom_refl, Category.id_comp, act]
    change (p j ⊗ₘ 𝟙 Z) ≫ (ρ_ (B j)).hom = (ρ_ (A j)).hom ≫ p j
    rw [tensorHom_id, rightUnitor_naturality]
  exact aux _ (fibreList_id j)

set_option backward.isDefEq.respectTransparency false in
/-- Right unit of binary ordered list splitting, including empty word. -/
theorem std_join_right_unit (xs : List X) :
    eqToHom (congrArg (fold 𝒮 Z A) (List.append_nil xs).symm) ≫
      join additiveStructure A xs [] = (ρ_ (fold 𝒮 Z A xs)).inv := by
  induction xs with
  | nil =>
    change 𝟙 _ ≫ (λ_ Z).inv = (ρ_ Z).inv
    monoidal
  | cons x xs ih =>
    have h : eqToHom (congrArg (fold 𝒮 Z A) (List.append_nil (x::xs)).symm) =
        A x ◁ eqToHom (congrArg (fold 𝒮 Z A) (List.append_nil xs).symm) := by
      rw [whiskerLeft_eqToHom]
    rw [h, std_join_cons, ← whiskerLeft_comp_assoc, ih]
    monoidal


def castOrder {xs ys : List X} (e : xs = ys) : AddressOrder X xs ys :=
  e ▸ .ident xs

theorem castOrder_map {xs ys : List X} (e : xs = ys) :
    AddressOrder.mapSum additiveStructure A (castOrder e) = eqToHom (congrArg (fold 𝒮 Z A) e) := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_list_congr {xs ys : List Y} (e : xs = ys) :
    eqToHom (congrArg (fun zs => fold 𝒮 Z A (zs.flatMap L)) e) ≫ rowsChart A L ys =
      rowsChart A L xs ≫ eqToHom (congrArg (fold 𝒮 Z (fun y => fold 𝒮 Z A (L y))) e) := by
  cases e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_one (y : Y) :
    eqToHom (congrArg (fold 𝒮 Z A) (List.append_nil (L y)).symm) ≫
      rowsChart A L [y] ≫ (ρ_ (fold 𝒮 Z A (L y))).hom = 𝟙 _ := by
  simp only [rowsChart, Category.assoc]
  let J : fold 𝒮 Z A (L y ++ []) ⟶ fold 𝒮 Z A (L y) ⊗ Z := join additiveStructure A (L y) []
  change eqToHom (congrArg (fold 𝒮 Z A) (List.append_nil (L y)).symm) ≫ J ≫
      (𝟙 (fold 𝒮 Z A (L y)) ⊗ₘ 𝟙 Z) ≫ (ρ_ _).hom = 𝟙 _
  rw [tensorHom_id, id_whiskerRight, Category.id_comp, ← Category.assoc, std_join_right_unit,
    Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
theorem standardPushSplit_right_unit {n m : Nat} (f : Fin n → Fin m) (A : Fin n → C) (j : Fin m) :
    standardPushSplit f id A j ≫ standardPushSingle (standardPushObj f A) j = 𝟙 _ := by
  let e : fibreList id j = [j] := fibreList_id j
  let a : fibreList (id ∘ f) j = ([j] : List (Fin m)).flatMap (fibreList f) :=
    (List.append_nil (fibreList f j)).symm
  let b : ([j] : List (Fin m)).flatMap (fibreList f) = (fibreList id j).flatMap (fibreList f) :=
    congrArg (fun l => l.flatMap (fibreList f)) e.symm
  rw [standardPushSplit_choice _ _ _ _ (castOrder (a.trans b)), castOrder_map]
  have aux (ys : List (Fin m)) (e : ys = [j]) :
      (eqToHom (congrArg (fold 𝒮 Z A) (a.trans (congrArg (fun l => l.flatMap (fibreList f)) e.symm))) ≫
        rowsChart A (fibreList f) ys) ≫
        (eqToHom (congrArg (fold 𝒮 Z (standardPushObj f A)) e) ≫
          (ρ_ (standardPushObj f A j)).hom) = 𝟙 (standardPushObj f A j) := by
    subst ys
    simp only [eqToHom_refl, Category.id_comp, Category.assoc]
    exact rowsChart_one A (fibreList f) j
  exact aux _ e


theorem rowsChart_singletons_index (xs : List X) :
    (xs.flatMap (fun x => [x])) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, List.singleton_append] using congrArg (List.cons x) ih

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_singletons (L : X → List X) (H : ∀ x, L x = [x]) (xs : List X) :
    eqToHom (congrArg (fold 𝒮 Z A)
      (show xs = xs.flatMap L from (rowsChart_singletons_index xs).symm.trans
        (congrArg (fun J => xs.flatMap J) (funext H).symm))) ≫
      rowsChart A L xs ≫ act 𝒮 Z (fun x =>
        eqToHom (congrArg (fold 𝒮 Z A) (H x)) ≫ (ρ_ (A x)).hom) xs =
    𝟙 (fold 𝒮 Z A xs) := by
  have h : L = fun x => [x] := funext H
  subst L
  simp only [eqToHom_refl, Category.id_comp]
  induction xs with
  | nil => simp only [rowsChart, act, eqToHom_refl, Category.id_comp, fold]
  | cons a xs ih =>
    let F := fold 𝒮 Z A
    let p (x : X) : F [x] ⟶ A x := (ρ_ (A x)).hom
    let l := xs.flatMap (fun x => [x])
    have e : eqToHom (congrArg F (rowsChart_singletons_index (a::xs)).symm) =
        A a ◁ eqToHom (congrArg F (rowsChart_singletons_index xs).symm) := by
      rw [whiskerLeft_eqToHom]
    change eqToHom (congrArg F (rowsChart_singletons_index (a::xs)).symm) ≫
      (join additiveStructure A [a] l ≫ (𝟙 (F [a]) ⊗ₘ rowsChart A (fun x => [x]) xs)) ≫
        (p a ⊗ₘ act 𝒮 Z p xs) = _
    rw [e, Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    let J : F (a::l) ⟶ F [a] ⊗ F l := join additiveStructure A [a] l
    have j : J ≫ (p a ▷ F l) = 𝟙 (A a ⊗ F l) := by
      unfold J p
      rw [std_join_cons, std_join_nil]
      monoidal
    calc
      _ = (A a ◁ eqToHom (congrArg F (rowsChart_singletons_index xs).symm)) ≫ J ≫
          (p a ▷ F l) ≫ (A a ◁ (rowsChart A (fun x => [x]) xs ≫ act 𝒮 Z p xs)) := by
        rw [tensorHom_def]
      _ = _ := by
        rw [← Category.assoc J, j]
        change (A a ◁ eqToHom (congrArg F (rowsChart_singletons_index xs).symm)) ≫
          𝟙 (A a ⊗ F l) ≫
          (A a ◁ (rowsChart A (fun x => [x]) xs ≫ act 𝒮 Z p xs)) = 𝟙 (A a ⊗ F xs)
        rw [Category.id_comp, ← whiskerLeft_comp]
        rw [← whiskerLeft_id]
        exact congrArg (fun f => A a ◁ f) ih

set_option backward.isDefEq.respectTransparency false in
theorem standardPushSplit_left_unit {n m : Nat} (f : Fin n → Fin m) (A : Fin n → C) (j : Fin m) :
    standardPushSplit id f A j ≫ standardPushMap f (standardPushSingle A) j = 𝟙 _ := by
  let xs := fibreList f j
  let e : fibreList (f ∘ id) j = xs.flatMap (fibreList id) :=
    (rowsChart_singletons_index xs).symm.trans
      (congrArg (fun J => xs.flatMap J) (funext fibreList_id).symm)
  rw [standardPushSplit_choice _ _ _ _ (castOrder e), castOrder_map, Category.assoc]
  exact rowsChart_singletons A (fibreList id) fibreList_id xs


/-- Coefficient-independent transport of one permutation per addressed row
to the single flat word. Empty rows still contribute their own block. -/
def rowOrders {L M : Y → List X} (p : ∀ y, AddressOrder X (L y) (M y)) :
    (ys : List Y) → AddressOrder X (ys.flatMap L) (ys.flatMap M)
  | [] => .ident []
  | y::ys => (p y).parallel (rowOrders p ys)

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_rowOrders {L M : Y → List X} (p : ∀ y, AddressOrder X (L y) (M y))
    (ys : List Y) :
    AddressOrder.mapSum additiveStructure A (rowOrders p ys) ≫ rowsChart A M ys =
      rowsChart A L ys ≫
        act 𝒮 Z (fun y => AddressOrder.mapSum additiveStructure A (p y)) ys := by
  induction ys with
  | nil =>
    change 𝟙 Z ≫ 𝟙 Z = 𝟙 Z ≫ 𝟙 Z
    rfl
  | cons y ys ih =>
    let k := AddressOrder.mapSum additiveStructure A (p y)
    let r := AddressOrder.mapSum additiveStructure A (rowOrders p ys)
    change AddressOrder.mapSum additiveStructure A ((p y).parallel (rowOrders p ys)) ≫
        (join additiveStructure A (M y) (ys.flatMap M) ≫ (𝟙 _ ⊗ₘ rowsChart A M ys)) =
      (join additiveStructure A (L y) (ys.flatMap L) ≫ (𝟙 _ ⊗ₘ rowsChart A L ys)) ≫
        (k ⊗ₘ act 𝒮 Z (fun y => AddressOrder.mapSum additiveStructure A (p y)) ys)
    have e : AddressOrder.mapSum additiveStructure A ((p y).parallel (rowOrders p ys)) ≫
        join additiveStructure A (M y) (ys.flatMap M) =
      join additiveStructure A (L y) (ys.flatMap L) ≫ (k ⊗ₘ r) :=
      std_join_parallel A (p y) (rowOrders p ys)
    rw [← Category.assoc, e, Category.assoc, Category.assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun z => join additiveStructure A (L y) (ys.flatMap L) ≫ (k ⊗ₘ z)) ih


set_option backward.isDefEq.respectTransparency false in
theorem join_tail_congr (as : List X) {bs cs : List X} (e : bs = cs) :
    eqToHom (congrArg (fold 𝒮 Z A) (congrArg (fun xs => as ++ xs) e)) ≫
      join additiveStructure A as cs =
    join additiveStructure A as bs ≫ fold 𝒮 Z A as ◁ eqToHom (congrArg (fold 𝒮 Z A) e) := by
  cases e
  simp only [eqToHom_refl, Category.id_comp, whiskerLeft_id]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_concat (xs ys : List Y) :
    eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_append (f:=L) (xs:=xs) (ys:=ys)).symm) ≫
      rowsChart A L (xs ++ ys) ≫ join additiveStructure (fun y => fold 𝒮 Z A (L y)) xs ys =
    join additiveStructure A (xs.flatMap L) (ys.flatMap L) ≫
      (rowsChart A L xs ⊗ₘ rowsChart A L ys) := by
  induction xs with
  | nil =>
    let F := fold 𝒮 Z A
    let Q := fold 𝒮 Z (fun y => F (L y))
    let P : F (ys.flatMap L) ⟶ Q ys := rowsChart A L ys
    change 𝟙 _ ≫ P ≫ (λ_ (Q ys)).inv = (λ_ (F (ys.flatMap L))).inv ≫ (𝟙 Z ⊗ₘ P)
    rw [Category.id_comp, id_tensorHom, leftUnitor_inv_naturality]
  | cons y xs ih =>
    let F := fold 𝒮 Z A
    let B := fun y => F (L y)
    let Q := fold 𝒮 Z B
    let a := L y
    let b := xs.flatMap L
    let c := ys.flatMap L
    let d := (xs ++ ys).flatMap L
    let e : b ++ c = d := (List.flatMap_append (f:=L) (xs:=xs) (ys:=ys)).symm
    let j₂ : F (a ++ b) ⟶ F a ⊗ F b := join additiveStructure A a b
    let k : F d ⟶ Q (xs ++ ys) := rowsChart A L (xs ++ ys)
    let k₁ : F b ⟶ Q xs := rowsChart A L xs
    let k₂ : F c ⟶ Q ys := rowsChart A L ys
    let j' : Q (xs ++ ys) ⟶ Q xs ⊗ Q ys := join additiveStructure B xs ys
    let d₀ : F ((a ++ b) ++ c) ⟶ F (a ++ (b ++ c)) :=
      eqToHom (congrArg F (List.append_assoc a b c))
    change eqToHom (congrArg F ((List.append_assoc a b c).trans
        (congrArg (fun ts => a ++ ts) e))) ≫
      (join additiveStructure A a d ≫ (𝟙 (F a) ⊗ₘ k)) ≫
        join additiveStructure B (y::xs) ys =
      join additiveStructure A (a ++ b) c ≫ ((j₂ ≫ (𝟙 (F a) ⊗ₘ k₁)) ⊗ₘ k₂)
    have e₀ : eqToHom (congrArg F ((List.append_assoc a b c).trans
        (congrArg (fun ts => a ++ ts) e))) =
      d₀ ≫ eqToHom (congrArg F (congrArg (fun ts => a ++ ts) e)) :=
      (eqToHom_trans _ _).symm
    rw [e₀, std_join_cons]
    simp only [Category.assoc, id_tensorHom]
    rw [← Category.assoc (eqToHom _) (join additiveStructure A a d), join_tail_congr A a e]
    have ind : eqToHom (congrArg F e) ≫ k ≫ j' =
        join additiveStructure A b c ≫ (k₁ ⊗ₘ k₂) := ih
    calc
      _ = d₀ ≫ join additiveStructure A a (b ++ c) ≫
          (F a ◁ (eqToHom (congrArg F e) ≫ k ≫ j')) ≫ (α_ (F a) (Q xs) (Q ys)).inv := by
        simp only [whiskerLeft_comp, Category.assoc]
        have kEq := id_tensorHom (F a) k
        rw [kEq]
      _ = _ := by
        rw [ind, whiskerLeft_comp]
        let j₃ : F (b ++ c) ⟶ F b ⊗ F c := join additiveStructure A b c
        let j₄ : F ((a ++ b) ++ c) ⟶ F (a ++ b) ⊗ F c := join additiveStructure A (a ++ b) c
        have h : d₀ ≫ join additiveStructure A a (b ++ c) ≫ F a ◁ j₃ =
            j₄ ≫ j₂ ▷ F c ≫ (α_ (F a) (F b) (F c)).hom :=
          std_join_assoc A a b c
        simp only [Category.assoc]
        change d₀ ≫ join additiveStructure A a (b ++ c) ≫ F a ◁ j₃ ≫ F a ◁ (k₁ ⊗ₘ k₂) ≫ _ = _
        simp only [reassoc_of% h]
        have t : ((j₂ ≫ (𝟙 (F a) ⊗ₘ k₁)) ⊗ₘ k₂) =
            (j₂ ▷ F c) ≫ ((𝟙 (F a) ⊗ₘ k₁) ⊗ₘ k₂) := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
        rw [id_tensorHom] at t
        change _ = j₄ ≫ ((j₂ ≫ F a ◁ k₁) ⊗ₘ k₂)
        rw [t]
        have nat := associator_inv_naturality (𝟙 (F a)) k₁ k₂
        rw [id_tensorHom] at nat
        rw [nat, Iso.hom_inv_id_assoc]
        rw [id_tensorHom]


set_option backward.isDefEq.respectTransparency false in
theorem rowsChart_iterated {V : Type*} (R : V → List Y) (zs : List V) :
    eqToHom (congrArg (fold 𝒮 Z A) (List.flatMap_assoc (l:=zs) (f:=R) (g:=L)).symm) ≫
      rowsChart A L (zs.flatMap R) ≫ rowsChart (fun y => fold 𝒮 Z A (L y)) R zs =
    rowsChart A (fun z => (R z).flatMap L) zs ≫ act 𝒮 Z (fun z => rowsChart A L (R z)) zs := by
  induction zs with
  | nil =>
    change 𝟙 Z ≫ 𝟙 Z ≫ 𝟙 Z = 𝟙 Z ≫ 𝟙 Z
    simp only [Category.id_comp]
  | cons z zs ih =>
    let F := fold 𝒮 Z A
    let B := fun y => F (L y)
    let Q := fold 𝒮 Z B
    let m := R z
    let n := zs.flatMap R
    let a := m.flatMap L
    let b := zs.flatMap (fun z => (R z).flatMap L)
    let c := n.flatMap L
    let d := (m ++ n).flatMap L
    let e : b = c := (List.flatMap_assoc (l:=zs) (f:=R) (g:=L)).symm
    let e₂ : a ++ c = d := (List.flatMap_append (xs:=m) (ys:=n) (f:=L)).symm
    let P : F a ⟶ Q m := rowsChart A L m
    let P' : F c ⟶ Q n := rowsChart A L n
    let V' := fold 𝒮 Z (fun v => Q (R v)) zs
    let N' : Q n ⟶ V' := rowsChart B R zs
    let N : F b ⟶ V' :=
      rowsChart A (fun v => (R v).flatMap L) zs ≫ act 𝒮 Z (fun v => rowsChart A L (R v)) zs
    let J : F (a ++ b) ⟶ F a ⊗ F b := join additiveStructure A a b
    let J' : F (a ++ c) ⟶ F a ⊗ F c := join additiveStructure A a c
    let p' := congrArg F (congrArg (fun ts => a ++ ts) e)
    let q' := congrArg F e₂
    change eqToHom (p'.trans q') ≫ rowsChart A L (m ++ n) ≫
        (join additiveStructure B m n ≫ (𝟙 (Q m) ⊗ₘ N')) =
      (J ≫ (𝟙 (F a) ⊗ₘ rowsChart A (fun v => (R v).flatMap L) zs)) ≫
        (P ⊗ₘ act 𝒮 Z (fun v => rowsChart A L (R v)) zs)
    have h : eqToHom q' ≫ rowsChart A L (m ++ n) ≫ join additiveStructure B m n =
        J' ≫ (P ⊗ₘ P') := rowsChart_concat A L m n
    have h' : eqToHom p' ≫ J' = J ≫ F a ◁ eqToHom (congrArg F e) := join_tail_congr A a e
    have ih' : eqToHom (congrArg F e) ≫ P' ≫ N' = N := ih
    rw [← eqToHom_trans p' q']
    simp only [Category.assoc]
    rw [reassoc_of% h, ← Category.assoc (eqToHom p'), h']
    simp only [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    have e' : (F a ◁ eqToHom (congrArg F e)) ≫ (P ⊗ₘ (P' ≫ N')) = P ⊗ₘ N := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, ih']
    exact congrArg (fun k => J ≫ k) e'

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
