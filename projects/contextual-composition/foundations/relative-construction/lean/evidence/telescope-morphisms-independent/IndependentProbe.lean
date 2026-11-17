import ContextualComposition.TelescopeMorphisms
open CategoryTheory ContextualComposition.FiniteTelescope
open ContextualComposition.FiniteTelescope.ChainHom
-- Place two distinct endomaps in distinct blocks.
private abbrev X := singleton (G := typeSpan) (a := ()) (b := ()) Bool
private def e : X ⟶ X := singletonArrow (G := typeSpan) (TypeCat.ofHom (fun x : Bool => x))
private def z : X ⟶ X := singletonArrow (G := typeSpan) (TypeCat.ofHom (fun _ : Bool => false))
example : flattenArrow (ChainHom.cons (G := Chain typeSpan) e (.cons z (.nil ()))) ≠
    flattenArrow (ChainHom.cons (G := Chain typeSpan) z (.cons e (.nil ()))) := by
  intro h
  exact parallel_native_maps_distinct (congrArg (fun k => singletonArrow (G := typeSpan) (a := ()) (b := ()) (firstArrow k)) h)
