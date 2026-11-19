module
public import ContextualComposition.ContextadTriangleSchedule
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadScheduleDetection
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadLawTransport ContextadHorizontalLaws
open TelescopeSquares FibreValue ContextadPayloadModification ContextadCellWhisker
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (Y : PackedCuts.Psh.{u,max u v,u,v} B) {i j : Nat} {f g : Map S i j} (a b : Cell f g)
theorem globalDetect (e : ∀ A, (evalCell Y a A).hom = (evalCell Y b A).hom) (x) :
    (globalCell Y a).hom.app x = (globalCell Y b).hom.app x := by
  let A := grade _ _ x
  let y := payload _ _ x
  let I := incl (PackedFree.pow S Y j) A
  have h := congrArg I.map (NatTrans.congr_app (e A) y)
  exact ((includeCell a Y A y).symm.trans ((NativeCube.ofEq h).trans (includeCell b Y A y))).eq
theorem rawDetect (e : ∀ A, (evalCell Y a A).hom = (evalCell Y b A).hom) (x) :
    (rawCell Y a).hom.app x = (rawCell Y b).hom.app x := by
  let F := BlockEvaluation.global S Y i
  let G := BlockEvaluation.global S Y j
  have t : x = (F ⋙ F.strictInv).obj x := Functor.congr_obj F.asIsomorphism.unit_eq x
  have h := globalDetect Y a b e (F.obj x)
  have q := G.map_injective h
  exact ((appChange (rawCell Y a).hom t).trans ((NativeCube.ofEq q).trans (appChange (rawCell Y b).hom t).symm)).eq
theorem detect (p : ∀ x : (power S i).apex, Nonempty (Y.obj (op ((power S i).dest.obj x))))
    (e : ∀ A, (evalCell Y a A).hom = (evalCell Y b A).hom) : a = b := by
  have k (x) : a.grade.hom.app x = b.grade.hom.app x := by
    obtain ⟨z⟩ := p x
    let w := pair Y (power S i).dest x z
    exact (readGrade a Y w).symm.trans ((congrArg gradeMap (rawDetect Y a b e w)).trans (readGrade b Y w))
  have h : a.grade = b.grade := Iso.ext (NatTrans.ext (funext k))
  cases a; cases b; cases h; rfl
abbrev observer (B : Type u) [Category.{max u v} B] : PackedCuts.Psh.{u,max u v,u,v} B := (Functor.const _).obj (Cat.of B)
theorem observable : (∀ A, (evalCell (observer B) a A).hom = (evalCell (observer B) b A).hom) ↔ a=b :=
  ⟨detect (observer B) a b (fun x => ⟨(power S i).dest.obj x⟩),fun h _ => h ▸ rfl⟩
variable {n : Nat} {r s : Map S n 1}
theorem pathIff (p q : Path r s) :
    (∀ x, (composite p).grade.hom.app x = (composite q).grade.hom.app x) ↔
      (∀ A, paste (observer B) A p = paste (observer B) A q) := by
  constructor
  · intro h A; exact transport (observer B) A p q h
  · intro h
    have e := (observable (composite p) (composite q)).mp (fun A => (paste_eq (observer B) A p).symm.trans ((h A).trans (paste_eq (observer B) A q)))
    intro x; rw [e]
end ContextualComposition.GrothendieckStep.ContextadScheduleDetection
