module

public import ContextualComposition.RigGrid
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

/-!
# Monoidal input to finite distributor grids

This adapter identifies the additive middle swap with mathlib's canonical
braided middle-four and the additive nullary merge with its left unitor.
A symmetric additive presentation is in particular braided. An independent
multiplicative monoidal structure can be supplied as a second value via
`Binary.ofMonoidal` with an explicit instance argument.
-/

namespace ContextualComposition.RigGrid

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C]

abbrev Binary.ofMonoidal [MonoidalCategory C] : Binary (C := C) where
  obj a b := a ⊗ b
  map f g := f ⊗ₘ g
  map_id := id_tensorHom_id
  map_comp f g h k := (tensorHom_comp_tensorHom f h g k).symm

def Additive.ofBraided [MonoidalCategory C] [BraidedCategory C] : Additive (C := C) where
  sum := Binary.ofMonoidal
  zero := 𝟙_ C
  middle a b c d := {
    hom := tensorμ a b c d
    inv := tensorδ a b c d
    hom_inv_id := tensorμ_tensorδ a b c d
    inv_hom_id := tensorδ_tensorμ a b c d }
  middle_natural f g h k := tensorμ_natural f g h k
  mergeZero := λ_ (𝟙_ C)

end ContextualComposition.RigGrid
