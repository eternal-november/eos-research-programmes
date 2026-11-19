module
public import ContextualComposition.TaggedSquareRecognition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FrameRecognition
open CategoryTheory CategoryTheory.Functor Opposite
section General
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
def frame (I : A ⥤ B) {F X : B ⥤ C} {Y : A ⥤ C} (v : F ≅ X) (h : I ⋙ X = Y) : I ⋙ F ≅ Y :=
  isoWhiskerLeft I v ≪≫ eqToIso h
theorem mappedCast {F G : A ⥤ B} (e : F = G) (K : B ⥤ C) :
    whiskerRight (eqToHom e) K = eqToHom (congrArg (· ⋙ K) e) := by subst G; ext x; simp
theorem side (I : A ⥤ B) {F G X : B ⥤ C} (a : F ⟶ G) (l : F ≅ X) (r : G ≅ X) (p : a ≫ r.hom = l.hom)
    {Z W : A ⥤ C} (h : I ⋙ X = Z) (k : I ⋙ X = W) (e : Z = W) :
    whiskerLeft I a ≫ (frame I r k).hom = (frame I l h).hom ≫ eqToHom e := by
  subst Z; subst W; simp [frame]
  exact congrArg (whiskerLeft I) p
theorem middle (I : A ⥤ B) {F G X Y : B ⥤ C} (l : F ≅ X) (r : G ≅ Y) (j : X = Y)
    {Z W : A ⥤ C} (h : I ⋙ X = Z) (k : I ⋙ Y = W) (e : Z = W) :
    whiskerLeft I (l ≪≫ eqToIso j ≪≫ r.symm).hom ≫ (frame I r k).hom = (frame I l h).hom ≫ eqToHom e := by
  subst Y; subst Z; subst W
  ext x; simp [frame]
end General
universe u v
open TaggedFixedSquare TripleEvaluation TaggedSquareRecognition
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m k : Nat)
theorem firstCast : fa S Y n m k = eqToHom (congrArg (· ⋙ packOut S Y n m k) (firstFace S Y n m k)) :=
  (congrArg (whiskerRight · (packOut S Y n m k)) (SuffixCell.leftFace_spec S Y n m k)).trans (mappedCast _ _)
theorem lastCast : fb S Y n m k = eqToHom (congrArg (· ⋙ packOut S Y n m k) (lastFace S Y n m k)) :=
  (congrArg (whiskerRight · (packOut S Y n m k)) (SuffixCell.rightFace_spec S Y n m k)).trans (mappedCast _ _)
theorem sourceCast : fs S Y n m k = eqToHom (congrArg (· ⋙ packOut S Y n m k) (stages S Y n m k)) := mappedCast _ _
theorem targetCast : ft S Y n m k = eqToHom (congrArg (· ⋙ packOut S Y n m k) (fixedAssociativity S Y n m k)) := mappedCast _ _
end ContextualComposition.GrothendieckStep.FrameRecognition
