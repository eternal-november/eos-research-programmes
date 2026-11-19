module
public import ContextualComposition.ContextadSchedule
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadSchedule
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes TelescopeSquares NativeAssoc NativeTrace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option pp.universes false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
theorem post {C D E : Type*} [Category* C] [Category* D] [Category* E] {F G : C ⥤ D} (e : F = G) (H : D ⥤ E) : F ⋙ H = G ⋙ H := congrArg (· ⋙ H) e
theorem pre {C D E : Type*} [Category* C] [Category* D] [Category* E] (H : C ⥤ D) {F G : D ⥤ E} (e : F = G) : H ⋙ F = H ⋙ G := congrArg (H ⋙ ·) e
theorem twoHeadOne : (blocks S 2 1).first ⋙ (blocks S 1 1).first = (blocks S 1 2).first := (cut_first S 1 1).symm
theorem twoHeadTwo : (blocks S 2 2).first ⋙ (blocks S 1 1).first = (blocks S 1 3).first := (cut_first S 1 2).symm
theorem twoMidOne : (blocks S 2 1).first ⋙ (blocks S 1 1).rest = (blocks S 1 2).rest ⋙ (blocks S 1 1).first := (cut_rest S 1 1).symm
theorem twoMidTwo : (blocks S 2 2).first ⋙ (blocks S 1 1).rest = (blocks S 1 3).rest ⋙ (blocks S 1 2).first :=
  by
    rw [cut_first S 2 1,cut_first S 1 1,Functor.assoc,twoMidOne,← Functor.assoc,← cut_rest S 1 2,Functor.assoc]
theorem unaryLast : last S 0 = 𝟭 (Apex P) := rfl
theorem restLast (n : Nat) : (blocks S n 1).rest = last S n :=
  (post (rfl : (blocks S n 1).rest = _) (𝟭 _)).trans ((pre ((blocks S n 1).rest) (unaryLast S).symm).trans (cut_tip S n 0))
theorem twoTailOne : (blocks S 2 1).rest = (blocks S 1 2).rest ⋙ (blocks S 1 1).rest :=
  (restLast S 2).trans ((cut_tip S 1 1).symm.trans (pre ((blocks S 1 2).rest) (restLast S 1).symm))
theorem twoTailTwo : (blocks S 2 2).rest = (blocks S 1 3).rest ⋙ (blocks S 1 2).rest := by
  apply snoc_ext S 1
  · rw [cut_rest S 2 1,twoTailOne,Functor.assoc,cut_rest S 1 1,← Functor.assoc,← cut_rest S 1 2,Functor.assoc]
  · rw [cut_tip S 2 1,Functor.assoc,cut_tip S 1 1,cut_tip S 1 2]
variable {S} (f : Map S 2 1)
theorem nested : inside 2 f = inside 1 (inside 1 f) := by
  let a := (inside 2 f).grade
  let b := (inside 1 (inside 1 f)).grade
  apply opExt
  · apply (blocks S 2 1).ext
    · apply (blocks S 1 1).ext
      · exact (post (inHead 2 f) (blocks S 1 1).first).trans ((twoHeadTwo S).trans
          ((inHead 1 (inside 1 f)).symm.trans (pre b (twoHeadOne S).symm)))
      · change (a ⋙ (blocks S 2 1).first) ⋙ (blocks S 1 1).rest = (b ⋙ (blocks S 2 1).first) ⋙ (blocks S 1 1).rest
        rw [show a ⋙ (blocks S 2 1).first = _ from inHead 2 f,twoMidTwo,Functor.assoc,twoMidOne,← Functor.assoc,show b ⋙ (blocks S 1 2).rest = _ from inTail 1 (inside 1 f),Functor.assoc,inHead]
    · change (inside 2 f).grade ⋙ (blocks S 2 1).rest = (inside 1 (inside 1 f)).grade ⋙ (blocks S 2 1).rest
      rw [inTail 2 f,twoTailTwo,twoTailOne,← Functor.assoc,inTail]
      simpa only [Functor.assoc] using (pre (blocks S 1 3).rest (inTail 1 f).symm)
  · intro x
    have l := ContextadInsideCells.leg 2 f x
    have m := ContextadPayloadModification.appChange f.leg (Functor.congr_obj (twoTailTwo S) x)
    have r := ContextadInsideCells.leg 1 f ((blocks S 1 3).rest.obj x)
    have t := ContextadInsideCells.leg 1 (inside 1 f) x
    exact l.trans (m.trans (r.symm.trans t.symm))
end ContextualComposition.GrothendieckStep.ContextadSchedule
