module
public import ContextualComposition.ProjectedCharts
public import ContextualComposition.ChartTotalCell
public import ContextualComposition.RightEndpoints
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FibreEndpoints
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates MovingCell ProjectedCharts FibreReader
section General
variable {C D : Type*} [Category* C] [Category* D]
def SquareAt {F G H K : C ⥤ D} (c : F ≅ G) (q : H ≅ K) (r : G = K) (l : ∀ x, F.obj x = H.obj x) (x : C) : Prop :=
  c.hom.app x ≫ eqToHom (Functor.congr_obj r x) = eqToHom (l x) ≫ q.hom.app x
theorem entireSquare {F G H K : C ⥤ D} (c : F ≅ G) (q : H ≅ K) (r : G = K) (l : ∀ x, F.obj x = H.obj x)
    (h : ∀ x, SquareAt c q r l x) (e : F = H) : c.hom ≫ eqToHom r = eqToHom e ≫ q.hom := by
  apply NatTrans.ext
  funext x; simp only [NatTrans.comp_app,eqToHom_app]; exact h x
theorem leftFromSquare {F G H K : C ⥤ D} (c : F ≅ G) (q : H ≅ K) (r : G = K)
    (l : ∀ x, F.obj x = H.obj x) (s : ∀ x, c.hom.app x ≫ eqToHom (Functor.congr_obj r x) =
      eqToHom (l x) ≫ q.hom.app x) : F = H := by
  let e := c ≪≫ eqToIso r ≪≫ q.symm
  refine Functor.ext_of_iso e l ?_
  intro x
  change c.hom.app x ≫ (eqToHom r).app x ≫ q.inv.app x = _
  rw [eqToHom_app,← Category.assoc,s]
  simp
def sample {F G : C ⥤ D} (c : F ≅ G) (x : C) : WordTrace.Edge D := ⟨F.obj x,G.obj x,c.hom.app x⟩
theorem fromEdges {F G H K : C ⥤ D} (c : F ≅ G) (q : H ≅ K) (r : G = K) (k : ∀ x, sample c x = sample q x) :
    F = H ∧ (∀ l : F = H, c.hom ≫ eqToHom r = eqToHom l ≫ q.hom) := by
  let l : ∀ x, F.obj x = H.obj x := fun x => congrArg WordTrace.Edge.src (k x)
  have s (x) : SquareAt c q r l x := by
    have e := WordTrace.Edge.conjugate (l x) (Functor.congr_obj r x) (c.hom.app x) (q.hom.app x) (WordTrace.Edge.hom_heq (k x))
    unfold SquareAt; rw [e]; simp
  exact ⟨leftFromSquare c q r l s,entireSquare c q r l s⟩
theorem before {J : Type*} [Category* J] (O : J ⥤ C) {F G : C ⥤ D} (c : F ≅ G) (x : J) :
    sample (isoWhiskerLeft O c) x = sample c (O.obj x) := rfl
theorem after {E : Type*} [Category* E] (I : D ⥤ E) {F G : C ⥤ D} (c : F ≅ G) (x : C) :
    sample (isoWhiskerRight c I) x = WordTrace.Edge.map I (sample c x) := rfl
theorem recognizeMapped {F G : C ⥤ D} (c : F ≅ G) (x : C) {E K : Type*} [Category* E] [Category* K]
    (J : E ⥤ D) {U V : K ⥤ E} (q : U ≅ V) (w : K)
    (hl : F.obj x = J.obj (U.obj w)) (hr : G.obj x = J.obj (V.obj w))
    (h : HEq (c.hom.app x) (J.map (q.hom.app w))) :
    sample c x = WordTrace.Edge.map J (sample q w) :=
  WordTrace.Edge.eq_of (a:=sample c x) (b:=WordTrace.Edge.map J (sample q w)) hl hr h
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
variable (a : B)
noncomputable abbrev orig : oldL S Y a ≅ oldR S Y a :=
  isoWhiskerLeft (off S Y a) (isoWhiskerRight (BlockCompositor.compositor S Y a) (eff S Y a))
noncomputable def restricted : (inp S Y a ⋙ leftTotal S Y) ≅ (inp S Y a ⋙ rightTotal S Y) := isoWhiskerLeft (inp S Y a) (cell S Y)
noncomputable def fibreEdge (w : W S Y a) : WordTrace.Edge (Total (twice S Y) (𝟭 B)) :=
  WordTrace.Edge.map (eff S Y a) (sample (BlockCompositor.compositor S Y a) w)
theorem recognized (x : X S Y) : sample (cell S Y) x = fibreEdge S Y ((base S Y).obj x) (point S Y x) := by
  exact recognizeMapped (cell S Y) x (I S Y x) (BlockCompositor.compositor S Y (A S Y x)) (point S Y x) rfl rfl (heq_of_eq (component S Y x))
theorem atOld (x : (base S Y).Fiber a) : sample (orig S Y a) x = fibreEdge S Y a ((off S Y a).obj x) :=
  (before (off S Y a) (isoWhiskerRight (BlockCompositor.compositor S Y a) (eff S Y a)) x).trans (after (eff S Y a) (BlockCompositor.compositor S Y a) ((off S Y a).obj x))
theorem repEdge (x : (base S Y).Fiber a) : fibreEdge S Y ((base S Y).obj x.val) (point S Y x.val) = fibreEdge S Y a ((off S Y a).obj x) := by
  rcases x with ⟨x,rfl⟩; rfl
theorem agreeEdge (x : (base S Y).Fiber a) : sample (restricted S Y a) x = sample (orig S Y a) x :=
  (before (inp S Y a) (cell S Y) x).trans ((recognized S Y x.val).trans ((repEdge S Y a x).trans (atOld S Y a x).symm))
theorem leftRestrict : inp S Y a ⋙ leftTotal S Y = oldL S Y a :=
  (fromEdges (restricted S Y a) (orig S Y a) (rightRestrict S Y a) (agreeEdge S Y a)).1
theorem restrictCell :
    whiskerLeft (inp S Y a) (cell S Y).hom ≫ eqToHom (rightRestrict S Y a) =
      eqToHom (leftRestrict S Y a) ≫ (orig S Y a).hom :=
  (fromEdges (restricted S Y a) (orig S Y a) (rightRestrict S Y a) (agreeEdge S Y a)).2 (leftRestrict S Y a)
theorem totalVertical : SuffixCell.vertical (base S Y) (proj S Y) (leftOver S Y) (rightOver S Y) (cell S Y).hom :=
  fun x => (componentCast S Y x).choose_spec
end ContextualComposition.GrothendieckStep.FibreEndpoints
