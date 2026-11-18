import ContextualComposition.PayloadLaws
open CategoryTheory Opposite ContextualComposition.GrothendieckStep Families
namespace PayloadOrder
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
def mark (A : Type) : presheaf.obj (op A) ⥤ presheaf.obj (op A) where
  obj X := fun a => Bool × X a
  map f := fun a => TypeCat.ofHom (fun z => (z.1,(f a).hom z.2))
  map_id _ := rfl
  map_comp _ _ := rfl
def M : presheaf ⟶ presheaf where
  app A := (mark A.unop).toCatHom
  naturality _ _ _ := rfl
def X : presheaf.obj (op Bool) := fun b => if b then Bool else Empty
def z : ZeroPower.weighted presheaf Bool := pair _ _ ⟨Bool,rfl⟩ X
def deep : (Iterates.layer endpoints splitEndpoints presheaf 2).obj (op Bool) :=
  pair _ _ smallGrade (pair _ _ (fun _ => Unit) (fun _ => Bool))
noncomputable def two := (CoproductSpan.All.component splitEndpoints presheaf Bool 2).inverse.obj deep
noncomputable def whole (x : Σ n, Total presheaf
    (CoproductSpan.leg (CoproductSpan.All.src splitEndpoints) (CoproductSpan.All.dst splitEndpoints) Bool n)) :=
  (CoproductSpan.compare (CoproductSpan.All.src splitEndpoints) (CoproductSpan.All.dst splitEndpoints) Bool presheaf).obj x
open PayloadLaws.All
#check evaluationUnitDiagram (Y := presheaf) splitEndpoints Bool
#check evaluationCompDiagram splitEndpoints Bool M T
#check evaluationComp splitEndpoints Bool M T (whole ⟨0,z⟩)
#check evaluationComp splitEndpoints Bool M T (whole ⟨2,two⟩)
#check strongComponent splitEndpoints Bool presheaf
#check strongCell splitEndpoints Bool (M ≫ T)
-- Witness that reversing the payload arrows changes the empty fibre, even up to equivalence.
abbrev L := Option (Bool × Empty)
abbrev R := Bool × Option Empty
example : ((M ≫ T).app (op Bool)).toFunctor.obj X false = L := rfl
example : ((T ≫ M).app (op Bool)).toFunctor.obj X false = R := rfl
theorem onlyNone (x : L) : x = none := by
  cases x with
  | none => rfl
  | some z => exact z.2.elim
theorem inequivalent : ¬ Nonempty (L ≃ R) := by
  rintro ⟨e⟩
  have h : (false,none) = (true,none) := e.symm.injective <|
    (onlyNone (e.symm (false,none))).trans (onlyNone (e.symm (true,none))).symm
  exact Bool.noConfusion (congrArg Prod.fst h)
example : M ≫ T ≠ T ≫ M := by
  intro h
  have q := congrArg (fun k : presheaf ⟶ presheaf => (k.app (op Bool)).toFunctor.obj X false) h
  exact inequivalent ⟨Equiv.cast q⟩
-- Actual composite action on a payload arrow: preserve the marker and map the selected value.
def flip : wideGrade ⟶ wideGrade := fun _ => TypeCat.ofHom Bool.not
example : ((((M ≫ T).app (op Bool)).toFunctor.map flip) false).hom (some (false,true)) =
    some (false,false) := rfl
end PayloadOrder
