module
public import ContextualComposition.MovingFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ProjectedCharts
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates MovingCell
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
def IsTransport {x y : C} (f : x ⟶ y) : Prop := ∃ h : x = y, f = eqToHom h
theorem castMap (F : C ⥤ D) {x y} (h : x = y) : IsTransport (F.map (eqToHom h)) :=
  ⟨congrArg F.obj h,eqToHom_map F h⟩
theorem trans {x y z : C} {a : x ⟶ y} {b : y ⟶ z} (h : IsTransport a) (k : IsTransport b) : IsTransport (a ≫ b) := by
  obtain ⟨s,rfl⟩ := h; obtain ⟨t,rfl⟩ := k; exact ⟨s.trans t,by simp⟩
theorem strict {F G : C ⥤ D} (e : F ≅ G) (h : ∀ x, IsTransport (e.hom.app x)) : F = G :=
  Functor.ext_of_iso e (fun x => (h x).choose) (fun x => (h x).choose_spec)
theorem projected {F G : C ⥤ D} (p : D ⥤ E) (e : F ≅ G) (h : ∀ x, IsTransport (p.map (e.hom.app x))) :
    F ⋙ p = G ⋙ p := strict (isoWhiskerRight e p) h
theorem ofConst {F : C ⥤ D} (d : D) (h : F = (Functor.const C).obj d) {x y : C} (f : x ⟶ y) : IsTransport (F.map f) := by
  subst F; exact ⟨rfl,rfl⟩
theorem fibreProj (p : C ⥤ D) (d : D) {x y : p.Fiber d} (f : x ⟶ y) : IsTransport (p.map f.val) :=
  ofConst d (Functor.Fiber.fiberInclusion_comp_eq_const (p := p) (S := d)) f
theorem readOver (N : C ⥤ D) [N.Full] [N.Faithful] (Z : D → C) (j : ∀ x, N.obj (Z x) ≅ x) (b : D ⥤ E)
    (h : ∀ x, IsTransport (b.map (j x).hom)) :
    coordinates N (𝟭 D) Z j ⋙ N ⋙ b = b := projected b (counit N (𝟭 D) Z j) h
theorem alignOver {H : Type*} [Category* H] (N : C ⥤ D) [N.Full] [N.Faithful] (Z : D → C) (j : ∀ x, N.obj (Z x) ≅ x)
    (b : D ⥤ E) (F : C ⥤ H) (p : H ⥤ E) (k : F ⋙ p = N ⋙ b) (h : ∀ x, IsTransport (b.map (j x).hom)) :
    (coordinates N (𝟭 D) Z j ⋙ F) ⋙ p = b :=
  (congrArg (coordinates N (𝟭 D) Z j ⋙ ·) k).trans (readOver N Z j b h)
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev proj := FibreValue.proj (twice S Y)
theorem incl_id {G : WordTrace.Pr (B := B)} (a : B) {x y : G.obj (op a)} (f : x ⟶ y) :
    IsTransport ((FibreValue.proj G).map ((FibreValue.incl G a).map f)) :=
  fibreProj (FibreValue.proj G) a ((FibreValue.embed G a).map f)
theorem embed_cast (U : Span (B := B)) (a : B) {x y : Lift.value Y a U} (f : x ⟶ y) :
    IsTransport ((FibreTotal.projection Y U.dest U.source).map ((embed Y U a).map f)) :=
  fibreProj (FibreTotal.projection Y U.dest U.source) a ((FibreTotal.into Y U.dest U.source a).map f)
theorem refOver (i : Nat × Nat) : refL S Y i ⋙ proj S Y = FibreTotal.projection Y (full S i).dest (full S i).source :=
  (congrArg (fun T => Lift.total (cut S i) Y ⋙ T) (totalOver S Y i.1 i.2)).trans (Lift.over (cut S i) Y)
noncomputable abbrev chartF := (MovingCoordinates.chart S Y).functor
theorem matched : Sigma.desc (refL S Y) ⋙ proj S Y = chartF S Y ⋙ base S Y := by
  apply PackedFree.sigma_ext
  intro i
  exact (refOver S Y i).trans ((congrArg (· ⋙ base S Y) (chartAt S Y i)).trans (Lift.over (Lift.comp (cut S i) (tagged S i)) Y)).symm
theorem adjustCast (x : X S Y) : IsTransport ((base S Y).map ((adjust S Y x).hom)) := by
  unfold adjust
  rw [Iso.trans_hom,Functor.map_comp]
  simp only [eqToIso.hom,Functor.mapIso_hom]
  exact trans (castMap (base S Y) _) (embed_cast Y (pairSpan S) ((base S Y).obj x) ((nativeEquiv S Y ((base S Y).obj x)).counitIso.hom.app (point S Y x)))
theorem movedOver : L S Y ⋙ proj S Y = base S Y :=
  alignOver (chartF S Y) (rep S Y) (adjust S Y) (base S Y) (Sigma.desc (refL S Y)) (proj S Y) (matched S Y) (adjustCast S Y)
theorem lCast (x : X S Y) : IsTransport ((proj S Y).map ((MovingCell.left S Y x).hom)) := by
  rw [leftLaw]; unfold lFrame
  rw [Functor.map_comp]
  exact trans (incl_id _ _) (castMap _ _)
theorem leftOver : leftTotal S Y ⋙ proj S Y = base S Y :=
  (projected (proj S Y) (gauge (L S Y) (MovingCell.left S Y)) (lCast S Y)).trans (movedOver S Y)
theorem componentCast (x : X S Y) : IsTransport ((proj S Y).map ((cell S Y).hom.app x)) := by
  rw [component]; exact incl_id _ _
theorem rightOver : rightTotal S Y ⋙ proj S Y = base S Y :=
  (projected (proj S Y) (cell S Y) (componentCast S Y)).symm.trans (leftOver S Y)
end ContextualComposition.GrothendieckStep.ProjectedCharts
