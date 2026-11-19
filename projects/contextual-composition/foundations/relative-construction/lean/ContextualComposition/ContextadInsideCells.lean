module
public import ContextualComposition.ContextadAppendCells
public import ContextualComposition.ContextadActionCells
public import ContextualComposition.ContextadOuterCharts
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadInsideCells
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue ContextadRoutes ContextadLawTransport BoundaryPaste TelescopeSquares
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
universe u v
section General
variable {D E : Type*} [Category* D] [Category* E]
theorem alignPure {x y x' y' : D} {a : x ⟶ y} {b : x' ⟶ y'} (h : Aligned a b) (p : Pure b) : Pure a := by
  obtain ⟨rfl,rfl,q⟩ := h; simp at q; exact q ▸ p
theorem castIsoApp {F F' G G' : D ⥤ E} (f : F' = F) (g : G = G') (i : F ≅ G) (x) :
    Aligned ((eqToIso f ≪≫ i ≪≫ eqToIso g).hom.app x) (i.hom.app x) := ContextadOuterCharts.castApp f g i.hom x
end General
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (k : Nat) {i j : Nat} (r : Map S i j)
noncomputable abbrev mid := along (power S k).dest (power S i).source (power S j).source r.grade r.over
noncomputable abbrev route := (blocks S k i).cutFunctor ⋙ mid k r ⋙ (blocks S k j).joinFunctor
theorem normalize : (inside k r).grade = route k r := by
  let c := blocks S k i
  let d := blocks S k j
  apply d.ext
  · exact (d.first_assemble ..).trans ((congrArg ((c.cutFunctor ⋙ mid k r) ⋙ ·) d.join_first).symm)
  · exact (d.rest_assemble ..).trans ((congrArg ((c.cutFunctor ⋙ mid k r) ⋙ ·) d.join_rest).symm)
variable {r s : Map S i j} (a : Cell r s)
theorem midVertical : SuffixCell.vertical (power S i).source (power S j).source r.over s.over a.grade.hom :=
  fun x => pureEq (a.source x) ⟨_,rfl⟩
noncomputable abbrev core :=
  isoWhiskerLeft (blocks S k i).cutFunctor (isoWhiskerRight (SuffixCell.alongIsoCell (power S k).dest (power S i).source (power S j).source
    r.over s.over a.grade (midVertical a)) (blocks S k j).joinFunctor)
noncomputable def iso : (inside k r).grade ≅ (inside k s).grade :=
  eqToIso (normalize k r) ≪≫ core k a ≪≫ eqToIso (normalize k s).symm
theorem coreHead (x) : Pure ((power S (k+j)).source.map ((core k a).hom.app x)) := by
  let z := (blocks S k i).cutFunctor.obj x
  let h := (SuffixCell.alongIsoCell (power S k).dest (power S i).source (power S j).source r.over s.over a.grade (midVertical a)).hom.app z
  change Pure (((blocks S k j).joinFunctor ⋙ (power S (k+j)).source).map h)
  rw [(blocks S k j).join_source]
  exact pureMap (power S k).source (pureId _)
theorem head (x) : Pure ((power S (k+j)).source.map ((iso k a).hom.app x)) :=
  castPure _ _ _ (core k a) (coreHead k a) x
theorem coreTip (x) : Aligned ((power S (k+j)).dest.map ((core k a).hom.app x))
    ((power S j).dest.map (a.grade.hom.app ((blocks S k i).rest.obj x))) :=
  NativeCube.functorAlign (blocks S k j).join_dest _
theorem tip (x) : Aligned ((power S (k+j)).dest.map ((iso k a).hom.app x))
    ((power S j).dest.map (a.grade.hom.app ((blocks S k i).rest.obj x))) :=
  ((castIsoApp (normalize k r) (normalize k s).symm (core k a) x).map (power S (k+j)).dest).trans (coreTip k a x)
theorem leg (r : Map S i j) (x) : Aligned ((inside k r).leg.app x) (r.leg.app ((blocks S k i).rest.obj x)) :=
  ContextadOuterCharts.castApp _ _ (whiskerLeft (blocks S k i).rest r.leg) x
noncomputable def insideCell : Cell (inside k r) (inside k s) where
  grade := iso k a
  source := head k a
  endpoint := by
    apply NatTrans.ext; funext x
    exact (((tip k a x).comp (leg k s x)).trans ((NativeCube.ofEq (NatTrans.congr_app a.endpoint _)).trans (leg k r x).symm)).eq
end ContextualComposition.GrothendieckStep.ContextadInsideCells
