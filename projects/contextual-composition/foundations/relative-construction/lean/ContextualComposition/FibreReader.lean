module
public import ContextualComposition.MovingFrames
@[expose] public section
namespace ContextualComposition.GrothendieckStep.FibreReader
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativePacked PackedCuts BlockEvaluation CutCompositor NativeCleavage ChartRealization MovingCoordinates MovingCell
section General
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
theorem recognize (N : D ⥤ E) [N.Full] [N.Faithful] (U V : C ⥤ D) (F : C ⥤ E) (e : U ⋙ N ≅ F) (k : V ⋙ N ≅ F)
    (p : ∀ x, U.obj x = V.obj x) (h : ∀ x, e.hom.app x = N.map (eqToHom (p x)) ≫ k.hom.app x) : U = V := by
  refine Functor.ext_of_iso (Functor.fullyFaithfulCancelRight N (e ≪≫ k.symm)) p ?_
  intro x
  apply N.map_injective
  change N.map (N.preimage (e.hom.app x ≫ k.inv.app x)) = _
  rw [N.map_preimage,h]
  simp
def align {J K : Type*} [Category* J] [Category* K] (O : J ⥤ D) (N : C ≌ D) (P : C ⥤ K) (T : K ⥤ E) (L : D ⥤ E)
    (h : P ⋙ T = N.functor ⋙ L) : (O ⋙ N.inverse ⋙ P) ⋙ T ≅ O ⋙ L :=
  eqToIso (congrArg (fun H => O ⋙ N.inverse ⋙ H) h) ≪≫ isoWhiskerLeft O (isoWhiskerRight N.counitIso L)
end General
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (a : B)
abbrev inp := Functor.Fiber.fiberInclusion (p := base S Y) (S := a)
abbrev off := FibreTotal.out Y (pairSpan S).dest (pairSpan S).source a
abbrev leg := embed Y (pairSpan S) a
abbrev pick := Sigma.desc (fun i => embed Y (full S i) a ⋙ Sigma.incl (C := fun j => total Y (full S j)) i)
noncomputable abbrev N := nativeEquiv S Y a
noncomputable abbrev T := (MovingCoordinates.chart S Y).functor
theorem included : pick S Y a ⋙ T S Y = (N S Y a).functor ⋙ leg S Y a := by
  apply PackedFree.sigma_ext; intro i
  exact (congrArg (embed Y (full S i) a ⋙ ·) (chartAt S Y i)).trans (chartIncl S Y a i)
noncomputable abbrev fixedRead := off S Y a ⋙ (N S Y a).inverse ⋙ pick S Y a
noncomputable def adjustAt : fixedRead S Y a ⋙ T S Y ≅ inp S Y a :=
  align (off S Y a) (N S Y a) (pick S Y a) (T S Y) (leg S Y a) (included S Y a)
theorem repEq (x : (base S Y).Fiber a) : (read S Y).obj x.val = (fixedRead S Y a).obj x := by
  rcases x with ⟨x,rfl⟩; rfl
set_option maxHeartbeats 5500000 in
theorem adjusts (x : (base S Y).Fiber a) :
    (adjust S Y x.val).hom = (T S Y).map (eqToHom (repEq S Y a x)) ≫ (adjustAt S Y a).hom.app x := by
  rcases x with ⟨x,rfl⟩
  change _ = (T S Y).map (𝟙 _) ≫ _
  rw [Functor.map_id,Category.id_comp]
  unfold adjust adjustAt align
  simp only [Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app]
  rfl
theorem reader : inp S Y a ⋙ read S Y = fixedRead S Y a :=
  recognize (T S Y) _ _ (inp S Y a) (isoWhiskerLeft (inp S Y a) (recover S Y)) (adjustAt S Y a)
    (repEq S Y a) (adjusts S Y a)
end ContextualComposition.GrothendieckStep.FibreReader
