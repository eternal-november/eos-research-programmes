module
public import ContextualComposition.NativeRawStructuralDiagram
@[expose] public section

/-! The actual dependent right-unit object has a singleton continuation
at every parent. The genuinely empty outer word is not replaced by it. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem dependentWordAug_rightUnit_chart {X : Type u} {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (xs : List X) (V : X → C) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    [hlax : ∀ x, (leftFactor T (V x)).LaxBraided] (hl : ∀ x, SameLeftGather T (V x) L) :
    dependentWordAug R L J xs (fun _ => [PUnit.unit]) V (fun _ (_ : PUnit.{u+1}) => I)
      (fun _ => (ρ_ I).hom) ε =
    wordAug (fun x => T.obj (V x) I) xs (act 𝒮 Zₐ (fun x => J.ρ (V x)) xs ≫ ε) := by
  let s : X → X × PUnit.{u+1} := fun x => (x, PUnit.unit)
  let B := fun x => T.obj (V x) I
  let A := B ∘ (Prod.fst : X × PUnit.{u+1} → X)
  let ys : X → List PUnit.{u+1} := fun _ => [PUnit.unit]
  let w := dependentWord xs ys
  let q := fun x => J.ρ (V x)
  let p := dependentWordAugCell R L J xs ys V (fun _ _ => I) (fun _ => (ρ_ I).hom) ε
  have hread : w.map Prod.fst = xs := by
    change (xs.flatMap (fun x => [s x])).map Prod.fst = xs
    rw [flatMap_single_eq_map s xs, List.map_map]
    exact List.map_id xs
  change wordAug A w p = wordAug B xs (act 𝒮 Zₐ q xs ≫ ε)
  apply wordAug_read_eq B Prod.fst w xs hread
  let e : fold 𝒮 Zₐ B xs = fold 𝒮 Zₐ A w :=
    (std_fold_map A s xs).symm.trans (congrArg (fold 𝒮 Zₐ A) (flatMap_single_eq_map s xs).symm)
  suffices key : eqToHom e ≫ p = act 𝒮 Zₐ q xs ≫ ε by
    exact (hom_source_pin_heq e p).symm.trans (heq_of_eq key)
  have hraw := dependentWordAug_raw_rows R L J xs ys V (fun _ _ => I)
    (fun _ => (ρ_ I).hom) ε
  have hδ (x : X) : eqToHom (std_fold_map id (fun _ : PUnit.{u+1} => I) (ys x)) ≫
      (ρ_ I).hom = (ρ_ I).hom := by simp
  rw [show (fun x => eqToHom (std_fold_map id (fun _ : PUnit.{u+1} => I) (ys x)) ≫ (ρ_ I).hom) =
      (fun x => (ρ_ I).hom) from funext hδ] at hraw
  change p = taggedRaggedRows A (fun x y => (x,y)) ys xs ≫ _ at hraw
  rw [hraw]
  have hr (x : X) : (Lin.left L (V x)).collect (fun _ : PUnit.{u+1} => I) (ys x) ≫
      T.map (𝟙 (V x)) (ρ_ I).hom ≫ q x = (ρ_ (B x)).hom ≫ q x := by
    have h := gatherLeft_singleton_unit L (V x) I (hl x)
    change (Lin.left L (V x)).collect id [I] ≫ T.map (𝟙 (V x)) (ρ_ I).hom = _ at h
    change (Lin.left L (V x)).collect id [I] ≫ T.map (𝟙 (V x)) (ρ_ I).hom ≫ q x = _
    rw [reassoc_of% h]
  rw [show (fun x => (Lin.left L (V x)).collect (fun _ : PUnit.{u+1} => I) (ys x) ≫
       T.map (𝟙 (V x)) (ρ_ I).hom ≫ q x) = (fun x => (ρ_ (B x)).hom ≫ q x) from funext hr]
  unfold taggedRaggedRows
  let k := fun x => eqToHom (std_fold_map A (fun y => (x,y)) (ys x))
  let u := fun x => (ρ_ (B x)).hom
  rw [← act_seq 𝒮 Zₐ u q xs]
  simp only [Category.assoc]
  have hu : act 𝒮 Zₐ k xs ≫ act 𝒮 Zₐ u xs = act 𝒮 Zₐ (fun x => k x ≫ u x) xs := act_seq 𝒮 Zₐ k u xs
  rw [← Category.assoc (act 𝒮 Zₐ k xs), hu]
  have hh := rowsChart_mapped_singletons A s (fun x => (ys x).map (fun y => (x,y))) (fun _ => rfl) xs
  let e₀ := std_fold_map A s xs
  let e₁ := congrArg (fold 𝒮 Zₐ A) (flatMap_single_eq_map s xs).symm
  change eqToHom e₁ ≫ rowsChart A (fun x => (ys x).map (fun y => (x,y))) xs ≫
    act 𝒮 Zₐ (fun x => k x ≫ u x) xs = eqToHom e₀ at hh
  change eqToHom (e₀.symm.trans e₁) ≫ _ = _
  rw [← eqToHom_trans e₀.symm e₁]
  simp only [Category.assoc]
  rw [reassoc_of% hh, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Right unit is an actual augmented isomorphism; its source uses the
original dependent gather and the continuation's actual singleton cell. -/
noncomputable def dependentRightUnitIso {X : Type u} {T : Bi (coeff (C:=C))}
    (R : Gather 𝒮 T Zₐ) (L : LeftGather 𝒮 T Zₐ) {I : C} (J : UnitCompat R I)
    (xs : List X) (V : X → C) (ε : fold 𝒮 Zₐ V xs ⟶ I)
    [hlax : ∀ x, (leftFactor T (V x)).LaxBraided] (hl : ∀ x, SameLeftGather T (V x) L)
    (ι : ∀ a, IsIso (J.ρ a)) (hn : xs.Nodup) :
    NativeAugmentedIso
      (dependentWordAug R L J xs (fun _ => [PUnit.unit]) V (fun _ (_ : PUnit.{u+1}) => I)
        (fun _ => (ρ_ I).hom) ε)
      (wordAug V xs ε) := by
  let A := fun x => T.obj (V x) I
  let φ (x) : A x ≅ V x := by
    let _ := ι (V x)
    exact asIso (J.ρ (V x))
  let p := act 𝒮 Zₐ (fun x => J.ρ (V x)) xs ≫ ε
  have hp : AddressOrder.mapSum additiveStructure A (.ident xs) ≫
      act 𝒮 Zₐ (fun x => (φ x).hom) xs ≫ ε = p := by
    change 𝟙 _ ≫ p = p
    exact Category.id_comp _
  exact (wordAugIso A V (.ident xs) hn φ p ε hp).retarget
    (dependentWordAug_rightUnit_chart R L J xs V ε hl).symm rfl

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
