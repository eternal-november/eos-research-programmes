module
public import ContextualComposition.RepresentableTriangleFrame
public import ContextualComposition.RepresentableStrictFold
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliTriangle
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientCoherentPseudomonad AmbientHorizontalDiagrams
open RepresentableKleisli RepresentableKleisliConstraints RepresentableTriangleFrame RepresentableStrictFold
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
section Generic
variable {C : Type*} [Bicategory C] {a b c d : C}
variable (f : a ⟶ b) {s t : b ⟶ c} (q : c ⟶ d) (I : s ≅ t) (e : s = t)
theorem endFrame (h : I = eqToIso e) :
    whiskerRightIso (whiskerLeftIso f I.symm) q = eqToIso (congrArg (fun k => (f ≫ k) ≫ q) e.symm) := by
  subst I; subst t; apply Iso.ext; simp
end Generic
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A D E : B} (f : KH S A D) (g : KH S D E)
noncomputable abbrev h := AmbientHorizontalFrames.E S (KObj S E) T.unit
noncomputable abbrev m := M S (yObj D) T.mult
noncomputable abbrev n := M S (KObj S E) T.mult
noncomputable abbrev q := M S (yObj E) T.mult
noncomputable abbrev e := unit T D
set_option linter.defProp false in
def expandEq := castThree (action S 1) (e (D := D) T) (K S g) (q (E := E) T) (fold T (e (D := D) T) g)
set_option linter.defProp false in
def endEq := endFrame f (q (E := E) T) _ _ (expandEq T g)
noncomputable def expandLong :=
  longer (action S 1) f g (e (D := D) T) (h (E := E) T) (m (D := D) T) (n (E := E) T) (q (E := E) T)
    (squareE S T.unit g) (squareM S T.mult g) (assocIso T (yObj E)) (leftIso T (yObj E))
noncomputable def tailLong :=
  whiskerRightIso (whiskerLeftIso f ((action S 1).map₂Iso (leftUnit T g))) (q (E := E) T)
noncomputable def actualLong := reassociate T f (unit T D) g ≪≫ tailLong T f g
set_option linter.defProp false in
def replaceTail :=
  congrArg (fun h₀ =>
    (moveTail (f ≫ K S (unit T D)) (q (E := E) T) (squareM S T.mult g).symm ≪≫
      whiskerLeftIso ((f ≫ K S (unit T D)) ≫ K S (K S g)) (assocIso T (yObj E)) ≪≫
      moveHead f (K S (unit T D)) (K S (K S g)) (K S (q (E := E) T)) (q (E := E) T) ≪≫ h₀) ≪≫ tailLong T f g)
    (endEq T f g)
theorem longEq : expandLong T f g = actualLong T f g := replaceTail T f g
theorem comparison :
    actualLong T f g = shorter (action S 1) f g (unit T D) (m (D := D) T) (q (E := E) T) (rightIso T (yObj D)) := by
  rw [← longEq]
  refine (cutLong (action S 1) f g (e (D := D) T) (h (E := E) T) (m (D := D) T) (n (E := E) T) (q (E := E) T)
    (squareE S T.unit g) (squareM S T.mult g) (assocIso T (yObj E)) (leftIso T (yObj E))).trans ?_
  unfold normalizedLong
  exact (congrArg (fun t => front f (K S (unit T D)) (m (D := D) T) (K S g) (q (E := E) T) ≪≫
    whiskerLeftIso f t ≪≫ (α_ f (K S g) (q (E := E) T)).symm) (RepresentableTriangleInterchange.original T g)).trans
      (cutShort (action S 1) f g (unit T D) (m (D := D) T) (q (E := E) T) (rightIso T (yObj D))).symm
theorem original :
    (reassociate T f (unit T D) g).hom ≫ composeCell T (𝟙 f) (leftUnit T g).hom =
      composeCell T (rightUnit T f).hom (𝟙 g) := by
  have H := congrArg Iso.hom (comparison T f g)
  have l : composeCell T (𝟙 f) (leftUnit T g).hom = (tailLong T f g).hom := by
    unfold composeCell tailLong
    rw [id_whiskerRight,Category.id_comp]
    rfl
  have r : composeCell T (rightUnit T f).hom (𝟙 g) =
      (shorter (action S 1) f g (unit T D) (m (D := D) T) (q (E := E) T) (rightIso T (yObj D))).hom := by
    change (((rightUnit T f).hom ▷ K S g) ≫ _ ◁ (action S 1).map₂ (𝟙 g)) ▷ q (E := E) T = _
    rw [(action S 1).map₂_id]
    change (((rightUnit T f).hom ▷ K S g) ≫ _ ◁ (𝟙 (K S g))) ▷ q (E := E) T = _
    rw [Bicategory.whiskerLeft_id,Category.comp_id]
    rfl
  rw [l,r]
  exact H
end ContextualComposition.GrothendieckStep.RepresentableKleisliTriangle
