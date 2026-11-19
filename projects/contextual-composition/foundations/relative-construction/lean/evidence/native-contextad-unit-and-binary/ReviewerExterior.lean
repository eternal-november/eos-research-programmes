import MovingBaseProbe
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep TelescopeSquares SpanPayload.Power
namespace ReviewerExterior
open MovingBaseProbe
open scoped CategoryTheory.Prod
noncomputable section
set_option backward.isDefEq.respectTransparency false
def inc (A : Nat) : row A 1 ⟶ row A 2 :=
  ⟨⟨((𝟙 (0:Nat)) ×ₘ (𝟙 W.pt)),((show (1:Nat) ⟶ 2 from homOfLE (by decide)) ×ₘ (𝟙 W.pt)),PUnit.unit⟩,𝟙 _⟩
/-- Classification, not just one failed square: with all the native component laws
valid, the actual exterior square survives exactly the identity base arrows. -/
theorem square_iff {D A : Nat} (a : D ⟶ A) :
    (((Iterates.layer P S Y 2).map a.op).toFunctor ⋙ ContextadTensor.binary data Y D =
      ContextadTensor.binary data Y A ⋙ P.baseRestrict Y a) ↔ D = A := by
  constructor
  · intro h
    let obs := (gradeProjection (Y := Y) (e := P.extend D)) ⋙ CategoryTheory.Prod.snd Nat W
    have k := Functor.congr_hom (congrArg (· ⋙ obs) ((ContextadTensor.baseChange_iff data Y a).mp h)) (inc A)
    change [D] = eqToHom _ ≫ (show W.pt ⟶ W.pt from [A]) ≫ eqToHom _ at k
    simpa using k
  · rintro rfl
    have e : a = 𝟙 D := Subsingleton.elim _ _
    rw [e, P.baseRestrict_id Y S, op_id, Functor.map_id]
    rfl
end
end ReviewerExterior

