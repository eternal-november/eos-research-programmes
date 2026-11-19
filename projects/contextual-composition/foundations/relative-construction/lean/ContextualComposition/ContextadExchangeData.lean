module
public import ContextualComposition.ContextadDisjointCones
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadDisjointCut
open CategoryTheory CategoryTheory.Functor Opposite NativeBlocks SpanApex ContextadRoutes ContextadSchedule ContextadLawTransport
open TelescopeSquares NativeAssoc FibreValue NativeTrace NativeCleavage BoundaryPaste ContextadOuterCharts ContextadModification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split} (f g : Map S 2 1)
section Generic
variable {X D T : Type*} [Category* X] [Category* D] [Category* T] {π : D ⥤ T}
theorem cartAligned {x y x' y' : D} {a : x ⟶ y} {b : x' ⟶ y'} (e : Aligned a b) (c : Cartesian π b) : Cartesian π a := by
  obtain ⟨rfl,rfl,h⟩ := e; simp at h; exact h ▸ c
end Generic
theorem leftConeCart (p : gradeCart g) (x) : Cartesian (left P) ((leftCone f g).app x) :=
  cartAligned (leftTip f g x) (p _ (cartMove f x))
theorem rightConeCart (x) : Cartesian (left P) ((rightCone f g).app x) := by
  apply cartAligned (rightTip f g x)
  exact cartesianLift P.grades (𝟭 B) _ _
theorem moveBase (x) : (power S 2).source.map ((move f).app x) = f.leg.app ((blocks S 2 2).first.obj x) := rfl
theorem coneBase (x) : Aligned ((left P).map ((leftCone f g).app x)) ((left P).map ((rightCone f g).app x)) := by
  apply ((leftTip f g x).map (left P)).trans
  apply (NativeCube.functorAlign g.over ((move f).app x)).trans
  apply (NativeCube.ofEq (moveBase f x)).trans
  apply (ContextadPayloadModification.appChange f.leg (Functor.congr_obj (inHead 2 g).symm x)).trans
  exact (snocBase f _).symm.trans ((rightTip f g x).map (left P)).symm
abbrev sameHead := (headLeft f g).trans (headRight f g).symm
abbrev sameBase := congrArg (· ⋙ right P S) (sameHead f g)
theorem overCone (x) : (left P).map ((leftCone f g).app x) = eqToHom (Functor.congr_obj (sameBase f g) x) ≫ (left P).map ((rightCone f g).app x) := by
  simpa using (coneBase f g x).comm
noncomputable abbrev exchange (p : gradeCart g) := compare (left P) (leftCone f g) (rightCone f g) (sameBase f g) (overCone f g) (leftConeCart f g p) (rightConeCart f g)
theorem exchangeFac (p : gradeCart g) (x) : (exchange f g p).hom.app x ≫ (rightCone f g).app x = (leftCone f g).app x :=
  factorFac (left P) (leftCone f g) (rightCone f g) (sameBase f g) (overCone f g) (rightConeCart f g) x
theorem exchangePure (p : gradeCart g) (x) : Pure ((left P).map ((exchange f g p).hom.app x)) :=
  ⟨Functor.congr_obj (sameBase f g) x,factorOver (left P) (leftCone f g) (rightCone f g) (sameBase f g) (overCone f g) (rightConeCart f g) x⟩
noncomputable def assembled (p : gradeCart g) : (lhs f g).grade ≅ (rhs f g).grade :=
  mateIso P.grades (right P S) _ _ (sameHead f g) (exchange f g p) (exchangePure f g p)
theorem assembledHead (p : gradeCart g) (x) : Pure (gradeMap ((assembled f g p).hom.app x)) := mateGrade _ _ _ _ _ _ _ x
theorem assembledTip (p : gradeCart g) (x) : (NativeAssoc.last S 1).map ((assembled f g p).hom.app x) = (exchange f g p).hom.app x := by
  let J := (whiskeringRight (power S 4).apex _ _).obj (intoPullback (projectionData P.grades) (right P S))
  have h : J.map ((assembled f g p).hom) = mate P.grades (right P S) _ _ (sameHead f g) (exchange f g p).hom (exchangePure f g p) := J.map_preimage _
  exact congrArg (fun a => CategoryTheory.Limits.CategoricalPullback.Hom.snd a) (NatTrans.congr_app h x)
theorem wideLeg (x) : (wide f).leg.app x = (power S 2).dest.map ((move f).app x) := rfl
abbrev lastLeg (x) := g.leg.app ((leaf₂ S).obj x)
theorem leftLegAt (x) : Aligned ((lhs f g).leg.app x) ((right P S).map ((leftCone f g).app x) ≫ lastLeg g x) := by
  let a := (move f).app x
  have e := ContextadPayloadModification.appChange g.leg (Functor.congr_obj (tail₁ S) ((wide f).grade.obj x))
  have l := (ContextadInsideCells.leg 1 g ((wide f).grade.obj x)).trans e
  exact (l.comp (NativeCube.ofEq (wideLeg f x))).trans ((NativeCube.ofEq (g.leg.naturality a).symm).trans
    (((leftTip f g x).map (right P S)).symm.comp (Aligned.refl _)))
theorem serialTipAligned {n i j : Nat} (a : Map S n i) (b : Map S i j) (x : (power S n).apex)
    {X Y Z : B} (s : X ⟶ Y) (t : Y ⟶ Z) (h : Aligned (b.leg.app (a.grade.obj x)) s) (l : Aligned (a.leg.app x) t) :
    Aligned ((comp a b).leg.app x) (s ≫ t) := h.comp l
end ContextualComposition.GrothendieckStep.ContextadDisjointCut
