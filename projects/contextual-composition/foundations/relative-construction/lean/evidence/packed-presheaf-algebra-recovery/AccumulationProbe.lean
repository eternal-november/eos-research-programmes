import ContextualComposition.AccumulationAlgebra
open CategoryTheory Opposite ContextualComposition.GrothendieckStep PackedFree AccumulationAlgebra
namespace AccumulationProbe
inductive B | pt
instance : Category B where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
abbrev b := B.pt
def P : Endpoints.{0,0,0,0} B where
  grades := (Functor.const _).obj (Cat.of B)
  extend _ := 𝟭 _
  lift _ := 𝟙 _
theorem S : P.Split := ⟨fun _ => HEq.rfl,fun _ _ => HEq.rfl⟩
abbrev Z := P.grades
def a : (step S).obj Z ⟶ Z where
  app _ := gradeProjection.toCatHom
  naturality _ _ _ := rfl
def no : b ⟶ b := fun _ => false
def yes : b ⟶ b := fun _ => true
def x : Total Z (𝟭 B) := pair Z _ b b
def e (g p : b ⟶ b) : x ⟶ x := arrow g p
abbrev E := ((eval S a).app (op b)).toFunctor
abbrev I (n : Nat) := ((inc S Z n).app (op b)).toFunctor
example : E.map ((I 0).map yes) = yes := rfl
example : E.map ((I 1).map (e no yes)) = no := rfl
example : E.map ((I 1).map (e yes no)) = yes := rfl
example : E.map ((I 1).map (e no yes)) ≠ E.map ((I 0).map yes) := fun h => Bool.noConfusion (congrFun h false)
example : ¬ IsIso (E.map ((I 1).map (e no yes))) := by
  change ¬ IsIso no
  intro h
  have k := IsIso.hom_inv_id no
  have p := congrFun k false
  have q := congrFun k true
  change (inv no) false = false at p
  change (inv no) false = true at q
  exact Bool.noConfusion (p.symm.trans q)
abbrev nestedInput := pair ((step S).obj Z) (𝟭 B) b x
def outerArrow (g i p : b ⟶ b) : nestedInput ⟶ nestedInput := arrow g (e i p)
abbrev cuts (m n : Nat) := ((ChainPayload.layerMap (inc S Z m) S n ≫ inc S ((free S).obj Z) n).app (op b)).toFunctor
abbrev byStages := (((free S).map (eval S a) ≫ eval S a).app (op b)).toFunctor
abbrev byJoin := ((join S Z ≫ eval S a).app (op b)).toFunctor
example : byStages.map ((cuts 1 1).map (outerArrow no yes yes)) = no := rfl
example : byJoin.map ((cuts 1 1).map (outerArrow yes no no)) = yes := rfl
example : byJoin.map ((cuts 0 1).map (e no yes)) = no := rfl
example : byStages.map ((cuts 1 0).map (e yes no)) = yes := rfl
example : ((cuts 0 1).obj x).1 ≠ ((cuts 1 0).obj x).1 := by decide
end AccumulationProbe
