module
public import ContextualComposition.TelescopeInterpretation
@[expose] public section
namespace ContextualComposition.GrothendieckStep.EndpointInterpretation
open CategoryTheory CategoryTheory.Functor Opposite PackedFree
universe b w u v
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{w} B] (P Q : Endpoints.{b,w,u,max u v} B)
/-- A map of native grade presentations. The square compares endpoint pastes
after their grade reindexing functors have been identified. No component of
the comparison from the new endpoint to the old one must be invertible. -/
structure Map where
  grade : ∀ A : B, P.grades.obj (op A) ⥤ Q.grades.obj (op A)
  endpoint : ∀ A : B, grade A ⋙ Q.extend A ⟶ P.extend A
  grade_square : ∀ {A D : B} (f : D ⟶ A),
    (P.grades.map f.op).toFunctor ⋙ grade D = grade A ⋙ (Q.grades.map f.op).toFunctor
  endpoint_square : ∀ {A D : B} (f : D ⟶ A), HEq
    (pasteLift _ _ _ _ _ (P.lift f) (endpoint D))
    (pasteLift _ _ _ _ _ (endpoint A) (Q.lift f))
variable {P Q} (h : Map P Q) (S : P.Split) (R : Q.Split)
variable (Y : Bᵒᵖ ⥤ Cat.{max u v,u})
abbrev fibre (A : B) := restrict Y _ _ (h.grade A) (h.endpoint A)
theorem base {A D : B} (f : D ⟶ A) :
    P.baseRestrict Y f ⋙ fibre h Y D = fibre h Y A ⋙ Q.baseRestrict Y f :=
  (restrict_paste Y _ _ _ _ _ _ _).symm.trans ((restrict_congr Y _ _ (h.grade_square f) (h.endpoint_square f)).trans (restrict_paste Y _ _ _ _ _ _ _))
def onPayload : (step S).obj Y ⟶ (step R).obj Y where
  app A := (fibre h Y A.unop).toCatHom
  naturality _ _ f := congrArg Functor.toCatHom (base h Y f.unop)
def oneStep : step S ⟶ step R where
  app Y := onPayload h S R Y
  naturality _ _ f := by
    apply NatTrans.ext; funext A
    exact congrArg Functor.toCatHom (ChainPayload.base_square f _ _ (h.grade A.unop) (h.endpoint A.unop)).symm
abbrev packed := TelescopeInterpretation.extend S (monad R) (oneStep h S R ≫ generator R)
theorem onOne : generator S ≫ (packed h S R).toNatTrans = oneStep h S R ≫ generator R :=
  TelescopeInterpretation.read_extend S _ _
/-- On a single layer it is the actual Grothendieck restriction followed by
the target one-layer inclusion, as functors, not just on objects. -/
theorem oneLayer (A : B) :
    ((inc S Y 1).app (op A)).toFunctor ⋙ (((packed h S R).app Y).app (op A)).toFunctor =
      fibre h Y A ⋙ ((inc R Y 1).app (op A)).toFunctor :=
  congrArg Cat.Hom.toFunctor (NatTrans.congr_app (NatTrans.congr_app (onOne h S R) Y) (op A))
def layer : (n : Nat) → pow S Y n ⟶ pow R Y n
  | 0 => 𝟙 Y
  | n+1 => (step S).map (layer n) ≫ (oneStep h S R).app (pow R Y n)
theorem targetAction :
    TelescopeInterpretation.action S (monad R) (oneStep h S R ≫ generator R) Y =
      (oneStep h S R).app ((free R).obj Y) ≫ cons R Y := by
  change (_ ≫ inc R ((free R).obj Y) 1) ≫ join R Y = _
  rw [Category.assoc,AccumulationAlgebra.singleton_join]
  rfl
theorem row (n : Nat) :
    inc S Y n ≫ (packed h S R).app Y = layer h S R Y n ≫ inc R Y n := by
  rw [show (packed h S R).app Y = fold S (TelescopeInterpretation.action S (monad R) (oneStep h S R ≫ generator R) Y) (inc R Y 0) from rfl,inc_fold,targetAction]
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    change (step S).map (foldLayer S _ _ n) ≫ (oneStep h S R).app ((free R).obj Y) ≫ cons R Y =
      ((step S).map (layer h S R Y n) ≫ (oneStep h S R).app (pow R Y n)) ≫ inc R Y (n+1)
    rw [ih,Functor.map_comp_assoc,← Category.assoc ((step S).map (inc R Y n)),(oneStep h S R).naturality,Category.assoc,inc_cons,Category.assoc]
end ContextualComposition.GrothendieckStep.EndpointInterpretation
