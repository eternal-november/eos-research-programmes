module
public import ContextualComposition.NativeContextAdmissibility
@[expose] public section

/-! Discriminating regression: surjective display projections do not
impose surjectivity on the carrier maps of native morphisms. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

def NativeProjectionClass.surjections : NativeProjectionClass.{u} where
  admissible f := Function.Surjective f
  ident _ := Function.surjective_id
  equiv e := e.surjective
  comp p q := q.comp p
  pullback f _ hg := fun x =>
    let ⟨y,hy⟩ := hg (f x)
    ⟨⟨(x,y),hy.symm⟩,rfl⟩

/-- A literal cell on every ordered sum of units, including the empty sum. -/
def collapseUnitFibre {X : Type} : (xs : List X) → fold 𝒮 Zₐ (fun _ => Zₐ) xs ⟶ Zₐ
  | [] => 𝟙 _
  | _::xs => (𝟙 Zₐ ⊗ₘ collapseUnitFibre xs) ≫ (ρ_ Zₐ).hom

noncomputable def twoUnitTarget : Aug ℙ Zₐ :=
  totalAug ⟨2,fun _ => Zₐ⟩ (collapseUnitFibre (List.finRange 2))

noncomputable def mergeUnitNative : Hom ℙ (twoUnitTarget (C:=C)).base (twoUnitTarget (C:=C)).base :=
  ⟨fun _ => (0 : Fin 2),fun j => collapseUnitFibre (fibreList (fun _ : Fin 2 => (0 : Fin 2)) j)⟩

noncomputable def twoUnitSource : Aug ℙ Zₐ :=
  ⟨(twoUnitTarget (C:=C)).base,(mergeUnitNative (C:=C)).comp (twoUnitTarget (C:=C)).ε⟩

noncomputable def mergeUnitAug : AugHom ℙ (twoUnitSource (C:=C)) twoUnitTarget :=
  ⟨mergeUnitNative,rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem mergeUnit_empty_fibre :
    fibreList (mergeUnitNative (C:=C)).addr (1 : Fin 2) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have h := mem_fibreList.mp hi
  change (0 : Fin 2) = 1 at h
  exact (by decide : (0 : Fin 2) ≠ 1) h

set_option backward.isDefEq.respectTransparency false in
theorem mergeUnit_not_surjective : ¬ Function.Surjective (mergeUnitNative (C:=C)).addr := by
  intro h
  obtain ⟨i,hi⟩ := h (1 : Fin 2)
  change (0 : Fin 2) = 1 at hi
  exact (by decide : (0 : Fin 2) ≠ 1) hi

set_option backward.isDefEq.respectTransparency false in
theorem allowed_nonsurjective_context_map :
    ∃ (P Q : IndexedNativeFamily.Admissible (C:=C) (I:=Zₐ) (A:=PUnit.{u+1}) NativeProjectionClass.surjections)
      (p : P ⟶ Q), ¬ Function.Surjective ((p.hom PUnit.unit).native.addr) := by
  let F : IndexedNativeFamily (C:=C) PUnit.{u+1} Zₐ := fun _ => twoUnitSource
  let G : IndexedNativeFamily (C:=C) PUnit.{u+1} Zₐ := fun _ => twoUnitTarget
  let P : IndexedNativeFamily.Admissible (C:=C) (I:=Zₐ) (A:=PUnit.{u+1}) NativeProjectionClass.surjections :=
    ⟨F,fun x => ⟨⟨x,⟨(0 : Fin 2)⟩⟩,rfl⟩⟩
  let Q : IndexedNativeFamily.Admissible (C:=C) (I:=Zₐ) (A:=PUnit.{u+1}) NativeProjectionClass.surjections :=
    ⟨G,fun x => ⟨⟨x,⟨(0 : Fin 2)⟩⟩,rfl⟩⟩
  exact ⟨P,Q,IndexedNativeFamily.admitHom _ (fun _ => mergeUnitAug),mergeUnit_not_surjective⟩

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
