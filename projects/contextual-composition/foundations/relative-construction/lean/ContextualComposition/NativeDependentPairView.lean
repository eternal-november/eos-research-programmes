module
public import ContextualComposition.NativeFiniteViewArrow
@[expose] public section

/-! Arbitrary native dependent pairs have ordered views, including
variable child cardinalities and globally empty families. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

structure NativeDependentPair (I : C) where
  parent : Aug (standardPush (C:=C)) I
  child : Fin parent.base.n → Aug (standardPush (C:=C)) I

structure NativeDependentPairHom {I : C} (A B : NativeDependentPair I) where
  parent : AugHom (standardPush (C:=C)) A.parent B.parent
  child : ∀ x, AugHom (standardPush (C:=C)) (A.child x) (B.child (parent.native.addr x))

namespace NativeDependentPair
variable {I : C} (A : NativeDependentPair I)

/-- All actual child positions keep their own parent index. The dummy
tag only makes an ambient extension total; it is absent from all words. -/
abbrev ParentTag := ULift.{u} (Fin A.parent.base.n)
abbrev ChildTag := ULift.{u} (Option ((x : Fin A.parent.base.n) × Fin (A.child x).base.n))

def childTag (x : Fin A.parent.base.n) (i : Fin (A.child x).base.n) : A.ChildTag := ⟨some ⟨x,i⟩⟩

def childLabel : A.ChildTag → C
  | ⟨none⟩ => I
  | ⟨some ⟨x,i⟩⟩ => (A.child x).base.val i

def parentView : NativeFiniteView A.parent.base A.ParentTag where
  tag := ULift.up
  label x := A.parent.base.val x.down
  tag_injective := fun _ _ e => congrArg ULift.down e
  label_tag _ := rfl

def childView (x : Fin A.parent.base.n) : NativeFiniteView (A.child x).base A.ChildTag where
  tag := A.childTag x
  tag_injective := fun _ _ h => eq_of_heq (Sigma.mk.inj (Option.some.inj (congrArg ULift.down h))).2
  label := A.childLabel
  label_tag _ := rfl

noncomputable def childTagDecidableEq : DecidableEq A.ChildTag := Classical.decEq _

noncomputable def ordered : OrderedDependentAugData I where
  X := A.ParentTag
  U := A.ChildTag
  eqX := Classical.decEq _
  eqU := A.childTagDecidableEq
  xs := A.parentView.word
  us := fun x => (A.childView x.down).word
  V := A.parentView.label
  A := fun x => (A.childView x.down).label
  xs_unique := A.parentView.word_nodup
  us_unique := fun x _ => (A.childView x.down).word_nodup
  ε := A.parentView.augCell A.parent
  δ := fun x => (A.childView x.down).augCell (A.child x.down)

set_option backward.isDefEq.respectTransparency false in
theorem parent_recovers :
    wordAug A.ordered.V A.ordered.xs A.ordered.ε = A.parent :=
  A.parentView.aug_eq A.parent

set_option backward.isDefEq.respectTransparency false in
theorem child_recovers (x : A.ordered.X) :
    wordAug (A.ordered.A x) (A.ordered.us x) (A.ordered.δ x) = A.child x.down :=
  (A.childView x.down).aug_eq (A.child x.down)

theorem child_dummy_absent (x : A.ordered.X) : (⟨none⟩ : A.ChildTag) ∉ A.ordered.us x := by
  intro h
  obtain ⟨i,_,e⟩ := List.mem_map.mp h
  have e' : (some (Sigma.mk x.down i) : Option ((y : Fin A.parent.base.n) × Fin (A.child y).base.n)) = none := congrArg (fun z : A.ChildTag => z.down) e
  cases e'

end NativeDependentPair

namespace NativeDependentPairHom
variable {I : C} {A B : NativeDependentPair I} (p : NativeDependentPairHom A B)

def childFunction (_x : Fin A.parent.base.n) : A.ChildTag → B.ChildTag
  | ⟨none⟩ => ⟨none⟩
  | ⟨some ⟨y,i⟩⟩ => B.childTag (p.parent.native.addr y) ((p.child y).native.addr i)

theorem childFunction_tag (x : Fin A.parent.base.n) (i : Fin (A.child x).base.n) :
    p.childFunction x (A.childTag x i) =
      B.childTag (p.parent.native.addr x) ((p.child x).native.addr i) := by
  rfl

def parentFunction (x : A.ParentTag) : B.ParentTag := ⟨p.parent.native.addr x.down⟩

theorem parentView_compatible (x : Fin A.parent.base.n) :
    p.parentFunction (A.parentView.tag x) = B.parentView.tag (p.parent.native.addr x) :=
  rfl

end NativeDependentPairHom
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
