import ContextualComposition.MixedMates
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
namespace SingleSpan
-- Pointwise optional data: none is preserved, so some natural fibre arrows are missed.
def addNone (A : Type) : presheaf.obj (op A) ⥤ presheaf.obj (op A) where
  obj X := fun a => Option (X a)
  map f := fun a => TypeCat.ofHom (Option.map (f a).hom)
  map_id X := by funext a; ext z; cases z <;> rfl
  map_comp f g := by funext a; ext z; cases z <;> rfl
def T : presheaf ⟶ presheaf where
  app A := (addNone A.unop).toCatHom
  naturality _ _ _ := rfl
def fill : (addNone Bool).obj wideGrade ⟶ (addNone Bool).obj wideGrade :=
  fun _ => TypeCat.ofHom (fun _ => some true)
example : ¬ ∃ f : wideGrade ⟶ wideGrade, (addNone Bool).map f = fill := by
  rintro ⟨f,h⟩
  have e := congrArg (fun k : (addNone Bool).obj wideGrade ⟶ (addNone Bool).obj wideGrade =>
    (k false).hom none) h
  change (none : Option Bool) = some true at e
  cases e
def base : Bool ⟶ Bool := collapse ≫ selectPoint true
example : ¬ ∃ s : Bool ⟶ Bool, s ≫ base = 𝟙 Bool := by
  rintro ⟨s,h⟩; exact Bool.noConfusion (congrArg (fun k : Bool ⟶ Bool => k false) h)
def X : presheaf.obj (op Bool) := fun b => if b then Bool else Empty
def z : ZeroPower.weighted presheaf Bool := pair _ _ ⟨Bool,rfl⟩ X
def deep : (Iterates.layer endpoints splitEndpoints presheaf 2).obj (op Bool) :=
  pair _ _ smallGrade (pair _ _ (fun _ => Unit) (fun _ => Bool))
noncomputable def two := (CoproductSpan.All.component splitEndpoints presheaf Bool 2).inverse.obj deep
noncomputable def whole (x : Σ n, Total presheaf
    (CoproductSpan.leg (CoproductSpan.All.src splitEndpoints) (CoproductSpan.All.dst splitEndpoints) Bool n)) :=
  (CoproductSpan.compare (CoproductSpan.All.src splitEndpoints) (CoproductSpan.All.dst splitEndpoints) Bool presheaf).obj x
#check MixedMates.All.inverseDiagram splitEndpoints T base
#check MixedMates.All.evaluationDiagram splitEndpoints T base
#check MixedMates.All.evaluationLaw splitEndpoints T base (whole ⟨0,z⟩)
#check MixedMates.All.evaluationLaw splitEndpoints T base (whole ⟨2,two⟩)
example : ((presheaf.map base.op).toFunctor.obj ((addNone Bool).obj X)) false = Option Bool := rfl
end SingleSpan
