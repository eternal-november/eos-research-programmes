import ContextualComposition.TaggedBaseLaws
open CategoryTheory Opposite ContextualComposition.GrothendieckStep
open TaggedBaseLaws Families
#check taggedUnitLaw splitEndpoints presheaf Bool
#check taggedCompLaw splitEndpoints presheaf collapse (selectPoint true)
def zPayload : presheaf.obj (op Bool) := fun b => if b then Bool else Empty
def zInput : ZeroPower.weighted presheaf Bool :=
  pair _ _ ⟨Bool,rfl⟩ zPayload
example : (ZeroPower.eval presheaf Bool).obj zInput true = Bool := rfl
example : (ZeroPower.eval presheaf Bool).obj zInput false = Empty := rfl
example : ((presheaf.map (selectPoint true).op).toFunctor.obj zPayload) () = Bool := rfl
example : ((presheaf.map (selectPoint false).op).toFunctor.obj zPayload) () = Empty := rfl
#check Zero.compLaw presheaf collapse (selectPoint true) zInput
#check (taggedCompLaw splitEndpoints presheaf collapse (selectPoint true) ⟨0,zInput⟩)
#check (taggedCompLaw splitEndpoints presheaf collapse (selectPoint true) ⟨1, (CoproductSpan.All.component splitEndpoints presheaf Bool 1).inverse.obj Families.sourcePair⟩)
