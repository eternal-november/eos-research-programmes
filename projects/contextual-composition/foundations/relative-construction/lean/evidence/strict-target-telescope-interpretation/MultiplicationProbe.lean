import ContextualComposition.EndpointInterpretation
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree
namespace MultiplicationProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
abbrev B := Discrete Unit
abbrev b : B := ⟨()⟩
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of (Discrete Bool))
  extend _ := (Functor.const _).obj b
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => by apply heq_of_eq; apply Subsingleton.elim⟩
def erase : EndpointInterpretation.Map P P where
  grade _ := (Functor.const _).obj (Discrete.mk false)
  endpoint _ := 𝟙 _
  grade_square _ := rfl
  endpoint_square _ := by apply heq_of_eq; apply Subsingleton.elim
abbrev T := free S
abbrev kill := EndpointInterpretation.packed erase S S
def choose (n : Nat) : T ⟶ T := if n=2 then kill.toNatTrans else 𝟙 _
def badAt (Y : Bᵒᵖ ⥤ Cat.{0,0}) := desc S (fun n => inc S Y n ≫ (choose n).app Y)
theorem branch (Y : Bᵒᵖ ⥤ Cat.{0,0}) (n : Nat) :
    inc S Y n ≫ badAt Y = inc S Y n ≫ (choose n).app Y := inc_desc S _ n
def bad : T ⟶ T where
  app := badAt
  naturality {X Y} f := by
    apply pack_ext; intro n
    rw [← Category.assoc,inc_map,Category.assoc,branch,← Category.assoc (inc S X n),branch,Category.assoc,← (choose n).naturality,← Category.assoc (inc S X n),inc_map,Category.assoc]
example : (monad S).η ≫ bad = (monad S).η := by
  apply NatTrans.ext; funext Y
  exact (branch Y 0).trans (Category.comp_id _)
example : generator S ≫ bad = generator S := by
  apply NatTrans.ext; funext Y
  exact (branch Y 1).trans (Category.comp_id _)
abbrev Z : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Unit))
def word : (pow S Z 2).obj (op b) := pair _ _ (Discrete.mk true) (pair _ _ (Discrete.mk true) b)
abbrev nested := ChainPayload.layerMap (inc S Z 1) S 1 ≫ inc S (T.obj Z) 1
def head : (x : (T.obj Z).obj (op b)) → Bool
  | ⟨0,_⟩ => false
  | ⟨_+1,x⟩ => (show Discrete Bool from grade _ _ x).as
/-- Checking naturality, the unit and all singleton inputs does not suffice:
the multiplication square at an actual nested pair of singleton blocks fails. -/
theorem fails : join S Z ≫ bad.app Z ≠ (T.map (bad.app Z) ≫ bad.app (T.obj Z)) ≫ join S Z := by
  intro h
  have j := Functor.congr_obj (congrArg Cat.Hom.toFunctor (NatTrans.congr_app h (op b))) ((nested.app (op b)).toFunctor.obj word)
  exact Bool.noConfusion (congrArg head j)
end MultiplicationProbe
