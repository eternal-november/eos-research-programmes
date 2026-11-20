module
public import ContextualComposition.ContentActualBend
public import ContextualComposition.RepresentablePurePseudofunctor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentPurePin
open CategoryTheory CategoryTheory.Bicategory Opposite
open AmbientCoherentPseudomonad RepresentableKleisliBicategory RepresentableKleisliCoherent
open ContentActualBend ContentRepresentable
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency true
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split} (T : Data S)
variable {A D : B}

/-- The arrows used for content bending are the 1-cell opposite of the
corresponding ordinary-base pure arrows, in the covariant fibre chart. -/
theorem fromContext (f : A ⟶ D) :
    letI : Bicategory (Part Bᵒᵖ) := bicategory T
    letI : Bicategory (PartOp (B := B)) := content T
    pureArrow T f = strongArrow T ((RepresentablePurePseudofunctor.pure T).map f.op.toLoc) := rfl

end ContextualComposition.GrothendieckStep.ContentPurePin
