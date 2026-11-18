module
public import ContextualComposition.ChartRestriction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.MovingCoordinates
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked NativeCleavage
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
section Generic
variable {C D X : Type*} [Category* C] [Category* D] [Category* X]
variable (N : C ⥤ D) [N.Full] [N.Faithful] (F : X ⥤ D) (Z : X → C) (j : ∀ x, N.obj (Z x) ≅ F.obj x)
noncomputable def coordinates : X ⥤ C where
  obj := Z
  map {x y} f := N.preimage ((j x).hom ≫ F.map f ≫ (j y).inv)
  map_id x := by apply N.map_injective; simp
  map_comp f g := by apply N.map_injective; simp
noncomputable def counit : coordinates N F Z j ⋙ N ≅ F :=
  NatIso.ofComponents j fun _ => by simp [coordinates]
end Generic
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev total (U : Span (B := B)) := Total Y U.dest
abbrev T := Σ i, total Y (full S i)
abbrev X := total Y (pairSpan S)
noncomputable def chart : T S Y ≌ X S Y := by
  let _ (i : Nat × Nat) : (cut S i).functor.IsEquivalence := (blocks S i.1 i.2).strictIso.toEquivalence.isEquivalence_functor
  let _ : (untag S).functor.IsEquivalence := (untagIso S).toEquivalence.isEquivalence_functor
  let _ (i : Nat × Nat) : (Lift.total (cut S i) Y).IsEquivalence := SpanPayload.totalIsEquivalence _ _ _ _
  let _ : (Lift.total (untag S) Y).IsEquivalence := SpanPayload.totalIsEquivalence _ _ _ _
  exact (ZeroPower.Sum.equiv fun i => (Lift.total (cut S i) Y).asEquivalence).trans
    ((CoproductSpan.Distribute.gather Y (fun i => (fixed S i).dest)).asEquivalence.trans (Lift.total (untag S) Y).asEquivalence)
theorem chartAt (i : Nat × Nat) : Sigma.incl (C := fun j => total Y (full S j)) i ⋙ (chart S Y).functor =
    Lift.total (Lift.comp (cut S i) (tagged S i)) Y :=
  by
  let C := Lift.total (cut S i) Y
  have h : (tag (fixed S) i).functor ⋙ (untag S).functor = (tagged S i).functor := by
    change Sigma.incl i ⋙ Sigma.desc (tagPair S) = tagPair S i
    apply Functor.ext (fun _ => rfl)
  have k := (SpanPayload.total_comp Y (tag (fixed S) i).functor _ (tag (fixed S) i).dest (untag S).functor _ (untag S).dest)
  have t : Lift.total (tag (fixed S) i) Y ⋙ Lift.total (untag S) Y = Lift.total (tagged S i) Y := by
    apply k.trans
    unfold Lift.total
    congr 1
  exact (congrArg (C ⋙ ·) t).trans (SpanPayload.total_comp Y (cut S i).functor _ (cut S i).dest (tagged S i).functor _ (tagged S i).dest)
abbrev embed (U : Span (B := B)) (A : B) := SpanPayload.Power.fibreInclude A Y U.source U.dest
theorem chartIncl (A : B) (i : Nat × Nat) :
    embed Y (full S i) A ⋙ Lift.total (Lift.comp (cut S i) (tagged S i)) Y =
    Sigma.incl (C := coords S Y A) i ⋙ (nativeEquiv S Y A).functor ⋙ embed Y (pairSpan S) A :=
  (Lift.global (Lift.comp (cut S i) (tagged S i)) Y A).symm.trans
    (congrArg (· ⋙ embed Y (pairSpan S) A) (native_at S Y A i)).symm
abbrev base := FibreTotal.projection Y (pairSpan S).dest (pairSpan S).source
abbrev point (x : X S Y) : Lift.value Y ((base S Y).obj x) (pairSpan S) :=
  (FibreTotal.out Y (pairSpan S).dest (pairSpan S).source _).obj ⟨x,rfl⟩
noncomputable abbrev decode (x : X S Y) := (nativeEquiv S Y ((base S Y).obj x)).inverse.obj (point S Y x)
noncomputable def rep (x : X S Y) : T S Y :=
  let z := decode S Y x
  ⟨z.1,(embed Y (full S z.1) _).obj z.2⟩
noncomputable def adjust (x : X S Y) : (chart S Y).functor.obj (rep S Y x) ≅ x := by
  let A := (base S Y).obj x
  let z := decode S Y x
  let N := nativeEquiv S Y A
  let U := embed Y (pairSpan S) A
  let i := z.1
  have a := Functor.congr_obj (chartAt S Y i) ((embed Y (full S i) A).obj z.2)
  have b := Functor.congr_obj (chartIncl S Y A i) z.2
  exact eqToIso (a.trans b) ≪≫ U.mapIso (N.counitIso.app (point S Y x))
noncomputable abbrev read := coordinates (chart S Y).functor (𝟭 (X S Y)) (rep S Y) (adjust S Y)
noncomputable abbrev recover := counit (chart S Y).functor (𝟭 (X S Y)) (rep S Y) (adjust S Y)
end ContextualComposition.GrothendieckStep.MovingCoordinates
