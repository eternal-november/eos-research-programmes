import ContextualComposition.FinalCube
open CategoryTheory CategoryTheory.Functor
open ContextualComposition.GrothendieckStep.FinalCube
example {X Y : Mix.Grid} (F : Mix.Map X Y) (h : Mix.Diagram F) :
    (whiskerRight X.cell F.f' ≫ whiskerLeft X.q F.t) ≫ whiskerRight (eqToHom F.pd) Y.b' =
    whiskerLeft X.b (eqToHom F.pa) ≫ (whiskerRight F.s Y.p ≫ whiskerLeft F.g Y.cell) := by
  apply NatTrans.ext
  funext x
  simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, eqToHom_app] using h x
