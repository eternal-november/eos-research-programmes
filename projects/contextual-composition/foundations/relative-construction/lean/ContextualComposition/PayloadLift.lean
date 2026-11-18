module
public import ContextualComposition.EvalPaste
/-! A payload transformation sends the canonical payload lift to a cartesian lift with a naturality correction. Compare chosen base restrictions on the two strict fibres using their actual lifts. -/
@[expose] public section
namespace ContextualComposition.GrothendieckStep.PayloadLift
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage
universe b w k j u v
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{j} K]
variable {Y Z : Bᵒᵖ ⥤ Cat.{v,u}} (T : Y ⟶ Z) (e : K ⥤ B)
set_option backward.isDefEq.respectTransparency false in
theorem mapPayload {x y : Total Y e} (f : x ⟶ y) :
    payloadMap ((ChainPayload.fibreMap T e).map f) =
      (T.app (op (e.obj (grade Y e x)))).toFunctor.map (payloadMap f) ≫
        eqToHom (ChainPayload.target T (e.map (gradeMap f)) (payload Y e y)) := by
  change (Grothendieck.Hom.fiber ((Grothendieck.map (ChainPayload.cell T e)).map f.unop)).unop = _
  dsimp [Grothendieck.map,payloadMap]; simp; rw [unop_comp]; congr 1; apply eqToHom_unop
theorem mapLiftPayload (y : Total Y e) {k : K} (a : k ⟶ grade _ _ y) :
    payloadMap ((ChainPayload.fibreMap T e).map (pullLift Y e y a)) =
      eqToHom (ChainPayload.target T (e.map a) (payload Y e y)) := by
  exact (mapPayload T e (pullLift Y e y a)).trans ((congrArg (· ≫ _) ((T.app (op (e.obj k))).toFunctor.map_id _)).trans (Category.id_comp _))
theorem correctedCart (y : Total Z e) {k : K} (a : k ⟶ grade _ _ y)
    {z : Z.obj (op (e.obj k))} (h : z = (Z.map (e.map a).op).toFunctor.obj (payload Z e y)) :
    Cartesian gradeProjection (arrow (x := pair Z e k z) (y := y) a (eqToHom h)) := by
  subst z; exact cartesianLift Z e y a
theorem mapLiftCart (y : Total Y e) {k : K} (a : k ⟶ grade _ _ y) :
    Cartesian gradeProjection ((ChainPayload.fibreMap T e).map (pullLift Y e y a)) := by
  let f := (ChainPayload.fibreMap T e).map (pullLift Y e y a)
  have h : f = arrow (x := (ChainPayload.fibreMap T e).obj (pullObj Y e y a)) (y := (ChainPayload.fibreMap T e).obj y) a (eqToHom (ChainPayload.target T (e.map a) (payload Y e y))) :=
    (homEquiv _ _).injective (Sigma.ext rfl (heq_of_eq (mapLiftPayload T e y a)))
  exact (congrArg (Cartesian (gradeProjection (Y := Z) (e := e))) h).mpr (correctedCart (Z := Z) e ((ChainPayload.fibreMap T e).obj y) a _)
variable (p : K ⥤ B) (C : Cleavage p)
abbrev projection (G : Bᵒᵖ ⥤ Cat.{v,u}) := gradeProjection (Y := G) (e := e) ⋙ p
theorem over : ChainPayload.fibreMap T e ⋙ projection e p Z = projection e p Y := rfl
abbrev action (d : B) := SpanPayload.fibreFunctor (ChainPayload.fibreMap T e) (projection e p Z) (over T e p) d
theorem selectedCart {a d : B} (u : a ⟶ d) (y : (projection e p Y).Fiber d) :
    Cartesian (projection e p Z) ((ChainPayload.fibreMap T e).map (Reindex.lift (extendChoice Y e p C) u y)) :=
  composite (mapLiftCart T e y.val _) (C a (grade Y e y.val) (u ≫ eqToHom y.property.symm)).cart
noncomputable def after {a d : B} (u : a ⟶ d) : Change.Cone u (action T e p d) where
  act := Reindex.functor (extendChoice Y e p C) u ⋙ action T e p a
  lift y := (ChainPayload.fibreMap T e).map (Reindex.lift (extendChoice Y e p C) u y)
  over y := Reindex.lift_over _ _ y
  cart := selectedCart T e p C u
  natural {x y} f := by
    change (ChainPayload.fibreMap T e).map _ ≫ (ChainPayload.fibreMap T e).map _ = (ChainPayload.fibreMap T e).map _ ≫ (ChainPayload.fibreMap T e).map _
    exact ((ChainPayload.fibreMap T e).map_comp _ _).symm.trans ((congrArg (ChainPayload.fibreMap T e).map (Reindex.map_fac _ u f)).trans ((ChainPayload.fibreMap T e).map_comp _ _))
noncomputable def square {a d : B} (u : a ⟶ d) :
    Reindex.functor (extendChoice Y e p C) u ⋙ action T e p a ≅
      action T e p d ⋙ Reindex.functor (extendChoice Z e p C) u :=
  Change.iso (after T e p C u) (Change.before _ (Route.ofChoice _ u))
theorem square_fac {a d : B} (u : a ⟶ d) (x : (projection e p Y).Fiber d) :
    ((square T e p C u).hom.app x).val ≫ Reindex.lift (extendChoice Z e p C) u ((action T e p d).obj x) =
      (ChainPayload.fibreMap T e).map (Reindex.lift (extendChoice Y e p C) u x) :=
  Change.fac (after T e p C u) (Change.before _ (Route.ofChoice _ u)) x
open SpanPayload.Power SpanApex
variable {P : Endpoints.{b,w,k,j} B} (S : P.Split)
noncomputable def nativeSquare (n : Nat) {A D : B} (a : A ⟶ D) :
    Reindex.functor (payloadChoice Y S n) a ⋙ action T (positivePowers P S n).dest (positivePowers P S n).source A ≅
      action T (positivePowers P S n).dest (positivePowers P S n).source D ⋙ Reindex.functor (payloadChoice Z S n) a :=
  square T _ _ (powerChoice S n) a
noncomputable def iterateSquare {P : Endpoints.{b,w,u,v} B} (S : P.Split) (n : Nat) {A D : B} (a : A ⟶ D) :
    Reindex.functor (Evaluation.iterateChoice S Y n) a ⋙ action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) A ≅
      action (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) D ⋙ Reindex.functor (Evaluation.iterateChoice S Z n) a :=
  square (ChainPayload.layerMap T S (n+1)) (𝟭 B) (𝟭 B) baseChoice a
end ContextualComposition.GrothendieckStep.PayloadLift
