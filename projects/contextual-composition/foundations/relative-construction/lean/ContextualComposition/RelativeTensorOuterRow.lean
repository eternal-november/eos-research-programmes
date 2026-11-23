module
public import ContextualComposition.RelativeTensorMiddleRowChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.OuterRow
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe vB uB vC uC vD uD vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})
variable {a b : LocallyDiscrete Bᵒᵖ} (u : a ⟶ b)

def source (a : LocallyDiscrete Bᵒᵖ) : Cat := (rightInner (middleComposite M N) Y).obj a
def intermediate (a : LocallyDiscrete Bᵒᵖ) : Cat := Cat.of (Left (row M a.as.unop) N Y)
def target (a : LocallyDiscrete Bᵒᵖ) : Cat := (rightInner M (rightInner N Y)).obj a

def changeSource : source M N Y a ⥤ source M N Y b := ((rightInner (middleComposite M N) Y).map u).toFunctor
def changeIntermediate : intermediate M N Y a ⥤ intermediate M N Y b := mapFirst (G := Y) (firstMap (Middle.change M u) N)
def changeTarget : target M N Y a ⥤ target M N Y b := ((rightInner M (rightInner N Y)).map u).toFunctor

def normalize (a : LocallyDiscrete Bᵒᵖ) : source M N Y a ⥤ intermediate M N Y a := (identifyFirst (middleRow M N a.as.unop) Y).functor
def rebracket (a : LocallyDiscrete Bᵒᵖ) : intermediate M N Y a ⥤ target M N Y a := associate (row M a.as.unop) N Y

theorem change_normalize : changeSource M N Y u ⋙ normalize M N Y b = normalize M N Y a ⋙ changeIntermediate M N Y u :=
  rightRow_change M N u Y

theorem change_rebracket : changeIntermediate M N Y u ⋙ rebracket M N Y b = rebracket M N Y a ⋙ changeTarget M N Y u :=
  first_naturality (X := row M a.as.unop) (X' := row M b.as.unop) (Middle.change M u) N Y

private theorem pasteRows (A B C A' B' C' : Type*) [Category* A] [Category* B] [Category* C]
    [Category* A'] [Category* B'] [Category* C']
    (f : A ⥤ B) (g : B ⥤ C) (f' : A' ⥤ B') (g' : B' ⥤ C')
    (u : A ⥤ A') (v : B ⥤ B') (w : C ⥤ C') (h : u ⋙ f' = f ⋙ v) (k : v ⋙ g' = g ⋙ w) :
    u ⋙ (f' ⋙ g') = (f ⋙ g) ⋙ w :=
  (congrArg (· ⋙ g') h).trans (congrArg (f ⋙ ·) k)

def component (a : LocallyDiscrete Bᵒᵖ) : source M N Y a ⥤ target M N Y a := normalize M N Y a ⋙ rebracket M N Y a

private theorem forward_assoc (Z : LocallyDiscrete C ⥤ᵖ Cat.{vM,uM}) :
    associate Z N Y = (associator Z N Y).functor := rfl

private theorem forward_trans {A B C : Type*} [Category* A] [Category* B] [Category* C] (e : A ≌ B) (f : B ≌ C) :
    e.functor ⋙ f.functor = (e.trans f).functor := rfl

theorem component_eq (a : LocallyDiscrete Bᵒᵖ) : component M N Y a = (rightRowAssociator M N Y a).functor := by
  unfold component rebracket normalize rightRowAssociator
  rw [forward_assoc N Y (row M a.as.unop)]
  exact forward_trans _ _

/-- Naturality at an arbitrary first-index arrow, including all native and balancing arrows in the three-factor carriers. -/
theorem naturality : changeSource M N Y u ⋙ component M N Y b = component M N Y a ⋙ changeTarget M N Y u :=
  pasteRows (source M N Y a) (intermediate M N Y a) (target M N Y a)
    (source M N Y b) (intermediate M N Y b) (target M N Y b)
    (normalize M N Y a) (rebracket M N Y a) (normalize M N Y b) (rebracket M N Y b)
    (changeSource M N Y u) (changeIntermediate M N Y u) (changeTarget M N Y u)
    (change_normalize M N Y u) (change_rebracket M N Y u)

end ContextualComposition.RelativeTensor.Iterated.OuterRow
