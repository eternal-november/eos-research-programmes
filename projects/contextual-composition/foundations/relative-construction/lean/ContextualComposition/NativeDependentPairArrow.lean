module
public import ContextualComposition.NativeDependentPairView
@[expose] public section

/-! The ordered views of arbitrary native dependent maps recover the
actual parent and each actual continuation arrow, including empty cells. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.NativeDependentPairHom
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {I : C} {A B : NativeDependentPair I} (p : NativeDependentPairHom A B)

set_option backward.isDefEq.respectTransparency false in
noncomputable def orderedMap :
    @OrderedDependentMap C _ _ _ A.ordered.X A.ordered.U B.ordered.X B.ordered.U
      B.ordered.eqX B.ordered.eqU A.ordered.xs A.ordered.us B.ordered.xs B.ordered.us
      A.ordered.V A.ordered.A B.ordered.V B.ordered.A := by
  letI := B.ordered.eqX
  letI := B.ordered.eqU
  exact
    { parent := p.parentFunction
      child := fun x => p.childFunction x.down
      parent_mem := NativeFiniteView.support A.parentView B.parentView p.parent.native p.parentFunction p.parentView_compatible
      child_mem := fun x _ => NativeFiniteView.support (A.childView x.down) (B.childView (p.parent.native.addr x.down))
        (p.child x.down).native (p.childFunction x.down) (p.childFunction_tag x.down)
      outer := NativeFiniteView.cellAt A.parentView B.parentView p.parent.native p.parentFunction p.parentView_compatible
      inner := fun x _ => NativeFiniteView.cellAt (A.childView x.down) (B.childView (p.parent.native.addr x.down))
        (p.child x.down).native (p.childFunction x.down) (p.childFunction_tag x.down) }

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
noncomputable def ordered : OrderedDependentAugArrow A.ordered B.ordered where
  map := p.orderedMap
  preserves := by
    letI := B.ordered.eqX
    letI := B.ordered.eqU
    constructor
    · exact NativeFiniteView.wordMap_preserves A.parentView B.parentView p.parent p.parentFunction p.parentView_compatible
    · intro x hx
      exact NativeFiniteView.wordMap_preserves (A.childView x.down) (B.childView (p.parent.native.addr x.down))
        (p.child x.down) (p.childFunction x.down) (p.childFunction_tag x.down)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem outer_recovers :
    letI := B.ordered.eqX
    letI := B.ordered.eqU
    HEq (p.ordered.map.outerNative B.ordered.xs_unique) p.parent.native := by
  letI := B.ordered.eqX
  letI := B.ordered.eqU
  unfold OrderedDependentMap.outerNative ordered orderedMap
  exact NativeFiniteView.wordMap_cells_heq A.parentView B.parentView p.parent.native p.parentFunction p.parentView_compatible

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem inner_recovers (x : A.ordered.X) (hx : x ∈ A.ordered.xs) :
    letI := B.ordered.eqX
    letI := B.ordered.eqU
    HEq (p.ordered.map.innerNative x hx (B.ordered.us_unique _ (p.ordered.map.parent_mem x hx)))
      (p.child x.down).native := by
  letI := B.ordered.eqX
  letI := B.ordered.eqU
  unfold OrderedDependentMap.innerNative ordered orderedMap
  exact NativeFiniteView.wordMap_cells_heq (A.childView x.down) (B.childView (p.parent.native.addr x.down))
    (p.child x.down).native (p.childFunction x.down) (p.childFunction_tag x.down)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.NativeDependentPairHom
