module
public import ContextualComposition.NativeContextExtension
@[expose] public section

/-! Place an arbitrary ordered dependent presentation in the indexed
context category, with its exact dependent-sum display leg. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

namespace OrderedDependentAugData
variable (D : OrderedDependentAugData I)
noncomputable def parentAug : Aug ℙ I := wordAug D.V D.xs D.ε
noncomputable def childAug (x : D.X) : Aug ℙ I := wordAug (D.A x) (D.us x) (D.δ x)

abbrev FinBranch := (i : Fin D.xs.length) × Fin (D.us D.xs[i]).length

def finBranchTags (z : D.FinBranch) : D.Branch := (D.xs[z.1],(D.us D.xs[z.1])[z.2])

theorem finBranchTags_mem (z : D.FinBranch) : D.finBranchTags z ∈ dependentWord D.xs D.us :=
  (dependentWord_mem _ _ _).mpr ⟨List.getElem_mem _,List.getElem_mem _⟩

set_option backward.isDefEq.respectTransparency false in
theorem finBranchTags_injective : Function.Injective D.finBranchTags := by
  intro ⟨i,j⟩ ⟨k,l⟩ e
  have h : D.xs[i] = D.xs[k] := congrArg Prod.fst e
  have hi : i = k := Fin.ext (D.xs_unique.getElem_inj.mp h)
  subst k
  have h' : (D.us D.xs[i])[j] = (D.us D.xs[i])[l] := congrArg Prod.snd e
  have hj : j = l := Fin.ext ((D.us_unique _ (List.getElem_mem _)).getElem_inj.mp h')
  subst l
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable def finBranchTagsEquiv :
    D.FinBranch ≃ {z // z ∈ dependentWord D.xs D.us} :=
  Equiv.ofBijective (fun z => ⟨D.finBranchTags z,D.finBranchTags_mem z⟩) (by
    constructor
    · exact fun x y h => D.finBranchTags_injective (congrArg Subtype.val h)
    · intro ⟨⟨x,y⟩,h⟩
      obtain ⟨hx,hy⟩ := (dependentWord_mem _ _ _).mp h
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
      obtain ⟨j,hj,k⟩ := List.mem_iff_getElem.mp hy
      exact ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,Subtype.ext (Prod.ext rfl k)⟩)

noncomputable def finiteBranchEquiv : Fin (D.accumulate R L J).base.n ≃ D.FinBranch :=
  (wordPositions (dependentWord D.xs D.us) (dependentWord_nodup D.xs_unique D.us_unique)).trans
    D.finBranchTagsEquiv.symm

end OrderedDependentAugData
namespace IndexedNativeFamily
variable {A : Type u}
variable (D : A → OrderedDependentAugData I)

noncomputable def orderedParent : IndexedNativeFamily (C:=C) A I := fun x => (D x).parentAug

noncomputable def orderedChildren : IndexedNativeFamily (C:=C) (orderedParent D).Extension I :=
  fun z => (D z.1).childAug ((D z.1).xs[z.2.down])

noncomputable def orderedAcc : IndexedNativeFamily (C:=C) A I := fun x => (D x).accumulate R L J

noncomputable def orderedExtension : (orderedAcc R L J D).Extension ≃ (orderedChildren D).Extension where
  toFun z :=
    let p := (D z.1).finiteBranchEquiv R L J z.2.down
    ⟨⟨z.1,⟨p.1⟩⟩,⟨p.2⟩⟩
  invFun z :=
    ⟨z.1.1,⟨((D z.1.1).finiteBranchEquiv R L J).symm ⟨z.1.2.down,z.2.down⟩⟩⟩
  left_inv := by
    intro ⟨x,⟨i⟩⟩
    exact congrArg (fun j => (⟨x,⟨j⟩⟩ : (orderedAcc R L J D).Extension))
      (((D x).finiteBranchEquiv R L J).symm_apply_apply i)
  right_inv := by
    intro ⟨⟨x,⟨i⟩⟩,⟨j⟩⟩
    exact congrArg (fun p : (D x).FinBranch => (⟨⟨x,⟨p.1⟩⟩,⟨p.2⟩⟩ : (orderedChildren D).Extension))
      (((D x).finiteBranchEquiv R L J).apply_symm_apply ⟨i,j⟩)

variable (K : NativeProjectionClass.{u})

structure OrderedAdmissible : Prop where
  parent : admissible K (orderedParent D)
  children : admissible K (orderedChildren D)

theorem orderedAcc_admissible (h : OrderedAdmissible D K) : admissible K (orderedAcc R L J D) := by
  let e := orderedExtension R L J D
  let f := (orderedChildren D).projection
  let g := (orderedParent D).projection
  exact K.comp (f:=f ∘ e) (g:=g) (K.comp (f:=e) (g:=f) (K.equiv e) h.children) h.parent

end IndexedNativeFamily
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
