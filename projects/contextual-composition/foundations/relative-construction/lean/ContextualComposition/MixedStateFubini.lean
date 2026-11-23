module

public import ContextualComposition.StagedStateDescent

/-! Inverting a chosen coordinate before further contraction and inverting its native images afterward give isomorphic categories. Composing this comparison with directed exchange gives the two orders of the independently marked contractions. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.StagedStateLocalization

open CategoryTheory Opposite DirectedStateBalance DirectedStateDiagramMap DirectedStateNativeFaithfulness DirectedStateIntertwiners
open DirectedStateIterates DirectedStateMarkedExchange DirectedStateModifications SelectiveStateContraction
universe u
variable {S T : Type u} [Category.{u} S] [Category.{u} T]
variable (Q : MorphismProperty S) (A : Index T ⥤ Index S ⥤ Cat.{u,u}) (P : MorphismProperty T)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev interim := (backData Q A P).descend
abbrev middleFunctor := map (install Q A)
abbrev newInsert (t : T) := insertion (strict (outerLocalized Q A)) t

theorem interim_row (t : T) : newInsert Q A t ⋙ interim Q A P = rowBack Q A P t :=
  congrFun (congrArg DirectedStateBalance.Cocone.fiber (restrict_descend (backData Q A P))) t

theorem middle_row (t : T) : outerInsert A t ⋙ middleFunctor Q A = innerQ Q A t t ⋙ newInsert Q A t :=
  insertion_natural (install Q A) t

theorem restore_row (t : T) : outerInsert A t ⋙ middleFunctor Q A ⋙ interim Q A P = outerInsert A t ⋙ late Q A P := by
  calc
    _ = (innerQ Q A t t ⋙ newInsert Q A t) ⋙ interim Q A P := congrArg (· ⋙ interim Q A P) (middle_row Q A t)
    _ = innerQ Q A t t ⋙ rowBack Q A P t := congrArg (innerQ Q A t t ⋙ ·) (interim_row Q A P t)
    _ = _ := rowBack_fac Q A P t

theorem restored : middleFunctor Q A ⋙ interim Q A P = late Q A P := by
  apply functor_ext (P:=middleFunctor Q A ⋙ interim Q A P) (Q:=late Q A P)
  · intro t x; exact Functor.congr_obj (restore_row Q A P t) x
  · intro t x y f; exact conjugate_heq (Conjugate.actions (restore_row Q A P t) f)
  · intro i j h x
    let moved := (innerQ Q A j i).obj x
    have e := (conjugate_eq (map_slide (install Q A) h x)).trans (move_conjugate (install Q A) h x)
    have e' := applied_slide (F:=strict (outerLocalized Q A)) (D:=Result A P Q) (backData Q A P) h moved
    exact conjugate_heq ((map_conjugate (interim Q A P) e).trans ((conjugate_eq e').trans (back_on Q A P h x)))

theorem to_from : toStaged Q A P ⋙ fromStaged Q A P = 𝟭 _ := by
  apply Localization.Construction.uniq
  calc
    _ = preview Q A P ⋙ fromStaged Q A P := congrArg (· ⋙ fromStaged Q A P) (toStaged_fac Q A P)
    _ = middleFunctor Q A ⋙ interim Q A P := congrArg (middleFunctor Q A ⋙ ·) (fromStaged_fac Q A P)
    _ = _ := restored Q A P

theorem reinstall_row (t : T) : rowBack Q A P t ⋙ toStaged Q A P = newInsert Q A t ⋙ outerQ Q A P := by
  apply Localization.Construction.uniq
  calc
    _ = outerInsert A t ⋙ late Q A P ⋙ toStaged Q A P :=
        congrArg (· ⋙ toStaged Q A P) (rowBack_fac Q A P t)
    _ = outerInsert A t ⋙ preview Q A P := congrArg (outerInsert A t ⋙ ·) (toStaged_fac Q A P)
    _ = _ := congrArg (· ⋙ outerQ Q A P) (middle_row Q A t)

theorem reinstalled : interim Q A P ⋙ toStaged Q A P = outerQ Q A P := by
  have row (t : T) : newInsert Q A t ⋙ interim Q A P ⋙ toStaged Q A P = newInsert Q A t ⋙ outerQ Q A P :=
    (congrArg (· ⋙ toStaged Q A P) (interim_row Q A P t)).trans (reinstall_row Q A P t)
  apply functor_ext (P:=interim Q A P ⋙ toStaged Q A P) (Q:=outerQ Q A P)
  · intro t x; exact Functor.congr_obj (row t) x
  · intro t x y f; exact conjugate_heq (Conjugate.actions (row t) f)
  · intro i j h x
    obtain ⟨z,rfl⟩ := (Localization.Construction.objEquiv (sel Q (A.obj (op j,i)))).surjective x
    let m := (slide (strict (outer A)) h).app z
    have e := applied_slide (F:=strict (outerLocalized Q A)) (D:=Result A P Q) (backData Q A P) h ((innerQ Q A j i).obj z)
    have a := map_conjugate (toStaged Q A P) ((conjugate_eq e).trans (back_on Q A P h z))
    have b := Conjugate.actions (toStaged_fac Q A P) m
    have c := map_conjugate (outerQ Q A P) ((conjugate_eq (map_slide (install Q A) h z)).trans (move_conjugate (install Q A) h z))
    exact conjugate_heq (a.trans (b.trans c))

theorem from_to : fromStaged Q A P ⋙ toStaged Q A P = 𝟭 _ := by
  apply Localization.Construction.uniq
  exact (congrArg (· ⋙ toStaged Q A P) (fromStaged_fac Q A P)).trans (reinstalled Q A P)

def stagedIso : IsoCat (Result A P Q) (Staged Q A P) where
  functor := toStaged Q A P
  inverse := fromStaged Q A P
  unit_eq := (to_from Q A P).symm
  counit_eq := from_to Q A P

/-- Both coordinate orders, with potentially different sets of slide generators inverted at the two respective stages. -/
def mixedExchange : IsoCat (Staged Q A P) (Staged P A.flip Q) :=
  (stagedIso Q A P).symm.trans ((localizedExchange A P Q).trans (stagedIso P A.flip Q))

end ContextualComposition.StagedStateLocalization
