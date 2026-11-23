module
public import ContextualComposition.RelativeTensorRowMapChange
public import ContextualComposition.RelativeTensorMixedOperations
public import ContextualComposition.RelativeTensorMiddleRowChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vM uM
variable {B : Type u} [Category.{v} B]

/-- Transport a commuting square along two identifications of its source diagrams, retaining the top arrow comparison. -/
def transportRowSquare {A : Type*} [Bicategory A] {b c b' c' d e : A}
    {f : b ⟶ c} {f' : b' ⟶ c'} (hb : b = b') (hc : c = c') (hf : HEq f f')
    (r : b ⟶ d) (t : c ⟶ e) (g : d ⟶ e) (p : f ≫ t ≅ r ≫ g) :
    f' ≫ Eq.mp (congrArg (fun k => k ⟶ e) hc) t ≅ Eq.mp (congrArg (fun k => k ⟶ d) hb) r ≫ g := by
  subst b'; subst c'
  cases eq_of_heq hf
  exact p

variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))

/-- The actual one-sided row multiplication used in mixed multiplication commutes with a change of input endpoint, up to its supplied invertible comparison. -/
def rowMultiplication_change (m : middleComposite M M ⟶ M) {a b : B} (u : a ⟶ b) :
    firstMap (Middle.change M u.op.toLoc) M ≫ rowMultiplication.{v,u,vM,uM} M m a ≅
      rowMultiplication.{v,u,vM,uM} M m b ≫ Middle.change M u.op.toLoc :=
  transportRowSquare (middleRow M M b) (middleRow M M a) (middleRow_change M M u.op.toLoc)
    (rowMap m b) (rowMap m a) (Middle.change M u.op.toLoc) (rowMap_changeIso m u)

end ContextualComposition.RelativeTensor.Iterated
