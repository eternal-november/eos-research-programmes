module
public import ContextualComposition.ContentComposition
public import ContextualComposition.ContentCompositionCells
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentNativeCompositionCells
open CategoryTheory CategoryTheory.Functor CategoryTheory.Bicategory Opposite
open AmbientCoherentPseudomonad RepresentableKleisli ContentActualBend ContentComposition ContentRepresentable
open RepresentableKleisliBicategory RepresentableKleisliCoherent
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split} (T : Data S)
variable {A D E : B}
abbrev write {X Y : B} := ContentComma.write P X Y
abbrev read {X Y : B} := ContentComma.read P X Y
noncomputable abbrev oldComp := RepresentableCommaComposition.comp (A := op E) (D := op D) (E := op A) T
abbrev forward {X Y : B} := (commaEquiv (S := S) (A := op Y) (D := op X)).inverse
abbrev backward {X Y : B} := (commaEquiv (S := S) (A := op Y) (D := op X)).functor

/-- Cell action of the native content multiplication over both actual
operands. The cell remains directed from the source composite to the
target composite in the covariant chart. -/
theorem nativeMap {x x' : Native (P := P) A D} {y y' : Native (P := P) D E}
    (t : x ⟶ x') (s : y ⟶ y') :
    HEq ((nativeComp T).map (X := (x,y)) (Y := (x',y')) (t,s)) (
    (read (P := P) (X := A) (Y := E)).map
      ((oldComp T).map (X := (dual y',dual x')) (Y := (dual y,dual x)) (((ContentComma.write P D E).map s).unop, ((ContentComma.write P A D).map t).unop)).op) := by
  let ta := (forward (S := S) (X := A) (Y := D)).map ((write (P := P)).map t).unop
  let sa := (forward (S := S) (X := D) (Y := E)).map ((write (P := P)).map s).unop
  let L := laws T (actualLast T) (actualPent T)
  have q := ContentCompositionCells.binaryMap (ops T) L
    (x := corepAt A) (y := corepAt D) (z := corepAt E) ta sa
  have z := congrArg (fun f => (read (P := P) (X := A) (Y := E)).map
    (((backward (S := S) (X := A) (Y := E)).map f).op)) q
  exact heq_of_eq z

end ContextualComposition.GrothendieckStep.ContentNativeCompositionCells
