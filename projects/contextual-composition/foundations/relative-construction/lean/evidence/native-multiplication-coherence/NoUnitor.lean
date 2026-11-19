import ContextualComposition.ContextadMixed
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeCleavage
namespace NoUnitor
noncomputable section
def P : Endpoints.{0,0,0,0} Nat where
  grades := (Functor.const _).obj (Cat.of (Discrete Bool))
  extend a := (Functor.const _).obj a
  lift f := { app := fun _ => f }
theorem S : P.Split where
  lift_id _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
  lift_comp _ _ := heq_of_eq (NatTrans.ext (funext fun _ => Subsingleton.elim _ _))
abbrev src := (power S 2).source
def tensor : (power S 2).apex ⥤ Apex P where
  obj x := pair _ _ (src.obj x) (Discrete.mk false)
  map f := arrow (src.map f) (𝟙 (Discrete.mk false))
  map_id _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (@Subsingleton.elim (Discrete.mk false ⟶ Discrete.mk false) _ _ _)))
  map_comp _ _ := (homEquiv _ _).injective (Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (@Subsingleton.elim (Discrete.mk false ⟶ Discrete.mk false) _ _ _)))
def m : ContextadTotal.Native S where
  grade := tensor
  over := rfl
  delta := { app := fun _ => 𝟙 _ }
  cart {x y} f _ := by
    have : IsIso (payloadMap (tensor.map f)) := (inferInstance : IsIso (𝟙 (Discrete.mk false)))
    exact ContextadCartesian.cart_of_payload _ _ (tensor.map f)
def d : ContextadUnit.Data P where
  grade _ := Discrete.mk true
  discharge _ := 𝟙 _
  reindex _ := rfl
  square _ := Subsingleton.elim _ _
def Y : Natᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of (Discrete Unit))
abbrev H (n : Nat) := PackedFree.pow S Y n
abbrev tag (x : Total (H 1) (𝟭 Nat)) : Discrete Bool := grade _ _ (payload _ _ x)
theorem allFalse (w : Total Y (power S 2).dest) :
    tag ((BlockEvaluation.global S Y 1).obj ((ContextadTotal.action m Y).obj w)) = Discrete.mk false := by
  have e := Functor.congr_obj (SpanPayload.total_projection Y (powerComparison S 0) _ (comparison_dest S 0)) ((ContextadTotal.action m Y).obj w)
  exact congrArg (fun g : chainApex S 0 => match g.2 with | .cons p _ => p) e
theorem output (A : Nat) (q : (H 2).obj (op A)) :
    grade _ _ ((ContextadCoherence.actual m Y A).obj q) = Discrete.mk false :=
  (congrArg (grade Y (P.extend A)) (Functor.congr_obj (ContextadFinal.identify m _ Y A (ContextadSpecialize.agrees m A)) q)).trans
    ((congrArg tag (Functor.congr_obj (ContextadRecognition.localIncl m A Y) q)).trans (allFalse _))
/-- No possible insertion functor can give even a comparison in this direction;
in particular neither chosen unit insertion can give an invertible unitor. -/
theorem impossible (A : Nat) (J : (H 1).obj (op A) ⥤ (H 2).obj (op A)) :
    IsEmpty (J ⋙ ContextadCoherence.actual m Y A ⟶ 𝟭 _) := by
  constructor
  intro n
  let z : (H 1).obj (op A) := pair _ _ (Discrete.mk true) (Discrete.mk ())
  have e := Discrete.eq_of_hom (gradeMap (n.app z))
  change (grade _ _ ((ContextadCoherence.actual m Y A).obj (J.obj z))).as = true at e
  rw [output] at e
  contradiction
example (A : Nat) :
    IsEmpty (ContextadUnit.atBase d (H 1) A ⋙ ContextadCoherence.actual m Y A ⟶ 𝟭 _) := impossible A _
example (A : Nat) :
    IsEmpty ((((PackedFree.step S).map ((ContextadUnit.unit d S).app Y)).app (op A)).toFunctor ⋙
      ContextadCoherence.actual m Y A ⟶ 𝟭 _) := impossible A _
end
end NoUnitor
