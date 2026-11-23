module

public import ContextualComposition.StrictStateProcessDiagram
public import ContextualComposition.DirectedStateBoundaries

/-! A pure state action erases two distinct native cells, while their diagonal insertions into directed balance remain distinct. -/

@[expose] public section
namespace ContextualComposition.NonfaithfulStateAction

open CategoryTheory CategoryTheory.Bicategory Opposite DirectedStateBalance DirectedStateBoundary StrictStateProcessDiagram
open oneState
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev O := Cat.of (Discrete Unit)
abbrev M := Cat.of oneState
abbrev L : Cat.{0,0} ⥤ Cat.{0,0} := (Functor.const _).obj O
abbrev R : Cat.{0,0} ⥤ Cat.{0,0} := 𝟭 _
abbrev G := homDiagram L R
abbrev process : O ⟶ M := ((Functor.const (Discrete Unit)).obj unitState).toCatHom
abbrev collapse : M ⟶ O := ((Functor.const oneState).obj (Discrete.mk ())).toCatHom
def original : process ⟶ process := 𝟙 _
def changed : process ⟶ process :=
  NatTrans.toCatHom₂ {app := fun _ => tick, naturality := fun _ _ _ => (Category.id_comp _).trans (Category.comp_id _).symm}

theorem different : original ≠ changed := fun e =>
  Nat.zero_ne_one (congrArg (fun m : process ⟶ process => m.toNatTrans.app ⟨()⟩) e)

theorem erased : (action (strict G) (𝟙 M) collapse).map original = (action (strict G) (𝟙 M) collapse).map changed := by
  apply Cat.Hom₂.ext; apply NatTrans.ext
  funext x; exact @Subsingleton.elim ((Discrete.mk () : Discrete Unit) ⟶ Discrete.mk ()) _ _ _

theorem native_distinction : (insertion (strict G) M).map original ≠ (insertion (strict G) M).map changed := by
  intro e
  let := StrictStateProcessDiagram.faithful L R M
  exact different ((insertion (strict G) M).map_injective e)

end ContextualComposition.NonfaithfulStateAction
