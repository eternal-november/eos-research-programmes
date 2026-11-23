module
public import ContextualComposition.NativeDependentOrderedRead
@[expose] public section

/-! Recover the exact ordered preservation equation of an actual
structural augmented arrow. Its address equality alone is not used
to infer preservation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem wordReadAugIso_preserves {X Y : Type u} {I : C} (A : X → C) (B : Y → C)
    (f : X ≃ Y) (xs : List X) (ys : List Y) (hx : xs.Nodup) (hy : ys.Nodup)
    (φ : ∀ x, A x ≅ B (f x))
    (a : fold 𝒮 Zₐ A xs ⟶ I) (b : fold 𝒮 Zₐ B ys ⟶ I)
    (v : NativeAugmentedIso (wordAug A xs a) (wordAug B ys b))
    (h : RawSingletonTrace (rawWordFrame A xs hx)
      ((rawWordFrame B ys hy).relabel f.symm f.symm.injective (B ∘ f)
        (fun x => congrArg B (f.apply_symm_apply x).symm))
      (fun x => (φ x).hom) v.hom.native)
    (o : AddressOrder X xs (ys.map f.symm)) :
    let e := (std_fold_map B f (ys.map f.symm)).symm.trans
      (congrArg (fold 𝒮 Zₐ B) (equiv_word_read f ys))
    AddressOrder.mapSum additiveStructure A o ≫ act 𝒮 Zₐ (fun x => (φ x).hom) (ys.map f.symm) ≫
      eqToHom e ≫ b = a := by
  intro e
  let w := ys.map f.symm
  let b₀ := eqToHom e ≫ b
  let G := (rawWordFrame B ys hy).relabel f.symm f.symm.injective (B ∘ f)
    (fun x => congrArg B (f.apply_symm_apply x).symm)
  let G₀ := rawWordFrame (B ∘ f) w (o.perm.nodup_iff.mp hx)
  let h₀ := wordAug_read_eq B f w ys (equiv_word_read f ys) b₀ b (hom_source_pin_heq e b)
  let Z := v.retarget rfl h₀.symm
  let Δ := wordFamily_read_eq B f w ys (equiv_word_read f ys)
  have hRead (i : Fin (wordFamily (B ∘ f) w).n) : G₀.read i = G.read (Fin.cast (congrArg Family.n Δ) i) := by
    change w[i] = f.symm ys[Fin.cast (congrArg Family.n Δ) i]
    have h := rawWordFrame_read_cast B f w ys (equiv_word_read f ys) i
    exact f.injective (h.trans (f.apply_symm_apply _).symm)
  have tr : RawSingletonTrace (rawWordFrame A xs hx) G₀ (fun x => (φ x).hom) Z.hom.native :=
    h.retarget rfl Δ.symm (NativeAugmentedIso.retarget_native_heq v rfl h₀.symm).symm
      (fun _ => rfl) (rawFrame_read_reverse G₀ G Δ hRead) (fun _ => HEq.rfl)
  have wtr := wordReindex_trace A (B ∘ f) o hx (o.perm.nodup_iff.mp hx) φ
  have k := tr.eq wtr (fun _ => rfl)
  have pres := Z.hom.preserves
  change Z.hom.native.comp (wordAug (B ∘ f) w b₀).ε = (wordAug A xs a).ε at pres
  rw [k] at pres
  exact (wordReindex_preserves_iff A (B ∘ f) o hx φ a b₀).mp pres

set_option backward.isDefEq.respectTransparency false in
theorem rawSingletonTrace_read_perm {X Y : Type u} {I : C} (A : X → C) (B : Y → C)
    (f : X ≃ Y) (xs : List X) (ys : List Y) (hx : xs.Nodup) (hy : ys.Nodup)
    (φ : ∀ x, A x ≅ B (f x)) {a : fold 𝒮 Zₐ A xs ⟶ I} {b : fold 𝒮 Zₐ B ys ⟶ I}
    (v : NativeAugmentedIso (wordAug A xs a) (wordAug B ys b))
    (h : RawSingletonTrace (rawWordFrame A xs hx)
      ((rawWordFrame B ys hy).relabel f.symm f.symm.injective (B ∘ f)
        (fun x => congrArg B (f.apply_symm_apply x).symm))
      (fun x => (φ x).hom) v.hom.native) :
    xs.Perm (ys.map f.symm) := by
  obtain ⟨e,c,_,he,_⟩ := h
  apply (List.perm_ext_iff_of_nodup hx (hy.map f.symm (fun _ _ neq eq => neq (f.symm.injective eq)))).mpr
  intro x
  constructor
  · intro hx
    rcases List.mem_iff_getElem.mp hx with ⟨i,hi,hr⟩
    have hh := he ⟨i,hi⟩
    change f.symm ys[e ⟨i,hi⟩] = xs[i] at hh
    exact List.mem_map.mpr ⟨ys[e ⟨i,hi⟩],List.getElem_mem _,hh.trans hr⟩
  · intro h
    rcases List.mem_map.mp h with ⟨y,hy,hr⟩
    rcases List.mem_iff_getElem.mp hy with ⟨j,hj,hs⟩
    have hh := he (e.symm ⟨j,hj⟩)
    change f.symm ys[e (e.symm ⟨j,hj⟩)] = xs[e.symm ⟨j,hj⟩] at hh
    rw [e.apply_symm_apply] at hh
    exact (hh.symm.trans ((congrArg f.symm hs).trans hr)) ▸ (List.getElem_mem _)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
