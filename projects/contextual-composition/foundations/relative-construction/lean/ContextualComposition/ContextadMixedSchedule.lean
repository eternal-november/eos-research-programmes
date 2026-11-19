module
public import ContextualComposition.ContextadSnocSchedule
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport
open TelescopeSquares NativeAssoc FibreValue ContextadChosenCone NativeTrace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (n : Nat) {i j : Nat} (f : Map S i j)
theorem mixedHead : (inside n (suffix f)).grade ⋙ front S (n+j) = front S (n+i) ⋙ (inside n f).grade := by
  apply (blocks S n j).ext
  · exact (congrArg ((inside n (suffix f)).grade ⋙ ·) (cut_first S n j).symm).trans
      ((inHead n (suffix f)).trans ((cut_first S n i).trans (congrArg (front S (n+i) ⋙ ·) (inHead n f)).symm))
  · exact (congrArg ((inside n (suffix f)).grade ⋙ ·) (cut_rest S n j).symm).trans
      ((congrArg (· ⋙ front S j) (inTail n (suffix f))).trans
      ((congrArg ((blocks S n (i+1)).rest ⋙ ·) (snocHead f)).trans
      ((congrArg (· ⋙ f.grade) (cut_rest S n i)).trans (congrArg (front S (n+i) ⋙ ·) (inTail n f)).symm)))
theorem mixedLast : (inside n (suffix f)).grade ⋙ last S (n+j) = (blocks S n (i+1)).rest ⋙ (suffix f).grade ⋙ last S j :=
  (congrArg ((inside n (suffix f)).grade ⋙ ·) (cut_tip S n j).symm).trans (congrArg (· ⋙ last S j) (inTail n (suffix f)))
noncomputable abbrev innerTip := whiskerLeft (blocks S n (i+1)).rest (snocArrow f)
theorem mixedTip (x) : Aligned ((snocArrow (inside n f)).app x) ((innerTip n f).app x) := by
  apply alignChosen P.grades (𝟭 B) (Functor.congr_obj (cut_tip S n i).symm x)
  · apply (snocBase _ x).trans
    apply (ContextadInsideCells.leg n f _).trans
    apply (ContextadPayloadModification.appChange f.leg (Functor.congr_obj (cut_rest S n i).symm x)).trans
    exact (snocBase f _).symm
  · exact snocPure _ _
  · exact snocPure _ _
theorem mixed : suffix (inside n f) = inside n (suffix f) := by
  apply opExt
  · apply snoc_ext S (n+j)
    · exact (snocHead (inside n f)).trans (mixedHead n f).symm
    · apply Eq.trans _ (mixedLast n f).symm
      apply conePure P.grades (𝟭 B) (snocArrow (inside n f)) (innerTip n f)
      · have l : (suffix (inside n f)).grade ⋙ last S (n+j) ⋙ left P =
            (front S (n+i) ⋙ (inside n f).grade) ⋙ (power S (n+j)).dest :=
          (congrArg ((suffix (inside n f)).grade ⋙ ·) (boundary S (n+j)).symm).trans (congrArg (· ⋙ _) (snocHead (inside n f)))
        have r : (inside n (suffix f)).grade ⋙ last S (n+j) ⋙ left P =
            (front S (n+i) ⋙ (inside n f).grade) ⋙ (power S (n+j)).dest :=
          (congrArg ((inside n (suffix f)).grade ⋙ ·) (boundary S (n+j)).symm).trans (congrArg (· ⋙ _) (mixedHead n f))
        exact l.trans (r.symm.trans (congrArg (· ⋙ left P) (mixedLast n f)))
      · exact (cut_tip S n i).symm
      · intro x
        exact (mixedTip n f x).map (left P)
      · exact snocPure _
      · exact fun _ => snocPure f _
  · intro x
    apply (snocLeg (inside n f) x).trans
    apply ((mixedTip n f x).map (right P S)).trans
    exact (snocLeg f _).symm.trans (ContextadInsideCells.leg n (suffix f) x).symm
end ContextualComposition.GrothendieckStep.ContextadSchedule
