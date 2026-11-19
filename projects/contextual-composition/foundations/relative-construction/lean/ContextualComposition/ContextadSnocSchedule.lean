module
public import ContextualComposition.ContextadSchedule
public import ContextualComposition.ContextadChosenCone
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadNativeLaws ContextadLawTransport ContextadCellPasting
open TelescopeSquares NativeAssoc FibreValue ContextadChosenCone
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 120000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {i j k : Nat} (f : Map S i j)
noncomputable def snocArrow : (suffix f).grade ⋙ last S j ⟶ last S i := by
  cases i with
  | zero => cases j with
    | zero => exact suffixRaw (P := P) (U := power S 0) (V := power S 0) f.grade f.leg
    | succ n => exact suffixRaw (P := P) (U := power S 0) (V := power S (n+1)) f.grade f.leg
  | succ m => cases j with
    | zero => exact suffixRaw (P := P) (U := power S (m+1)) (V := power S 0) f.grade f.leg
    | succ n => exact suffixRaw (P := P) (U := power S (m+1)) (V := power S (n+1)) f.grade f.leg
theorem snocHead : (suffix f).grade ⋙ front S j = front S i ⋙ f.grade := by cases i <;> cases j <;> rfl
theorem snocBase (x) : Aligned (gradeMap ((snocArrow f).app x)) (f.leg.app ((front S i).obj x)) := by cases i <;> cases j <;> exact Aligned.refl _
theorem snocPure (x) : Pure (payloadMap ((snocArrow f).app x)) := by cases i <;> cases j <;> exact pureId _
theorem snocLeg (x) : Aligned ((suffix f).leg.app x) ((right P S).map ((snocArrow f).app x)) := by cases i <;> cases j <;> exact Aligned.refl _
theorem outId (i : Nat) : suffix (identity (S := S) i) = identity (i+1) := by
  apply opExt
  · cases i <;> exact restrict_id P.grades _
  · intro x
    apply (snocLeg _ x).trans
    have h := alignChosen P.grades (𝟭 B) rfl ((snocBase (identity (S := S) i) x).trans (by
        have t := Functor.congr_obj (boundary S i) x
        exact ⟨t,t,by simp [identity,grade_id]⟩)) (snocPure _ x)
      (WeightedCells.totalPureId P.grades (𝟭 B) ((last S i).obj x))
    exact (h.map (right P S)).trans ((NativeCube.ofEq ((right P S).map_id _)).trans (by
      have d := Functor.congr_obj (last_dst S i) x
      exact ⟨d,d,by simp [identity]⟩))
def serial {U V W : Span (B := B)} (f : Operation U V) (g : Operation V W) : Operation U W :=
  ⟨f.grade ⋙ g.grade,(congrArg (f.grade ⋙ ·) g.over).trans f.over,pasteLift _ _ _ _ _ f.leg g.leg⟩
def reframe {U V U' V' : Span (B := B)} (a : U' = U) (b : V' = V) (f : Operation U V) : Operation U' V' := by
  cases a; cases b; exact f
theorem serialReframe {U V W U' V' W' : Span (B := B)} (a : U' = U) (b : V' = V) (c : W' = W)
    (f : Operation U V) (g : Operation V W) : serial (reframe a b f) (reframe b c g) = reframe a c (serial f g) := by
  cases a; cases b; cases c; rfl
theorem suffixFrame : suffix f = reframe (succ_power S i) (succ_power S j) (appendMap f) := by
  cases i <;> cases j <;> rfl
theorem frameGrade {U V U' V' : Span (B := B)} (a : U' = U) (b : V' = V) {f g : Operation U V} (h : f.grade = g.grade) :
    (reframe a b f).grade = (reframe a b g).grade := by cases a; cases b; exact h
theorem outComp (g : Map S j k) : suffix (comp f g) = comp (suffix f) (suffix g) := by
  apply opExt
  · change (suffix (comp f g)).grade = (serial (suffix f) (suffix g)).grade
    rw [suffixFrame,suffixFrame f,suffixFrame g,serialReframe]
    apply frameGrade
    exact restrict_paste P.grades (power S i).dest (power S j).dest (power S k).dest f.grade g.grade f.leg g.leg
  · intro x
    let a := (snocArrow g).app ((suffix f).grade.obj x)
    let b := (snocArrow f).app x
    have h₁ : Aligned (gradeMap ((snocArrow (comp f g)).app x)) (gradeMap (a ≫ b)) := by
      apply (snocBase (comp f g) x).trans
      exact (((snocBase g ((suffix f).grade.obj x)).trans (ContextadPayloadModification.appChange g.leg (Functor.congr_obj (snocHead f) x))).comp (snocBase f x)).symm
    have h := alignChosen P.grades (𝟭 B) rfl h₁ (snocPure _ x)
      (WeightedCells.totalPureComp _ _ (snocPure g _) (snocPure f _))
    apply (snocLeg _ x).trans
    apply (h.map (right P S)).trans
    exact (NativeCube.ofEq ((right P S).map_comp a b)).trans ((snocLeg g _).symm.comp (snocLeg f _).symm)
end ContextualComposition.GrothendieckStep.ContextadSchedule
