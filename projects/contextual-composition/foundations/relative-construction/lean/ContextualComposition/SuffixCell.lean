module
public import ContextualComposition.TripleCuts
@[expose] public section
namespace ContextualComposition.GrothendieckStep.SuffixCell
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SpanApex BoundaryPaste
set_option maxHeartbeats 90000
set_option backward.isDefEq.respectTransparency false
variable {B K J L : Type*} [Category* B] [Category* K] [Category* J] [Category* L]
variable (e : K ⥤ B) (p : J ⥤ B) (q : L ⥤ B)
variable {H T : J ⥤ L} (h : H ⋙ q = p) (t : T ⋙ q = p)
abbrev vertical (a : H ⟶ T) := ∀ x, q.map (a.app x) = eqToHom (Functor.congr_obj (h.trans t.symm) x)
theorem verticalEq (j : H = T) : vertical p q h t (eqToHom j) := by
  subst T; intro x; simp
def alongCell (a : H ⟶ T) (v : vertical p q h t a) : along e p q H h ⟶ along e p q T t where
  app x := ⟨⟨𝟙 x.fst,a.app x.snd,by
    change e.map (𝟙 x.fst) ≫ eqToHom ((along e p q T t).obj x).glue = eqToHom ((along e p q H h).obj x).glue ≫ q.map (a.app x.snd)
    simp [v]⟩⟩
  naturality x y f := by
    apply InducedCategory.hom_ext
    apply CategoricalPullback.hom_ext
    · change f.hom.fst ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.fst
      simp
    · exact a.naturality f.hom.snd
theorem suffixProj (a : H ⟶ T) (v : vertical p q h t a) :
    whiskerRight (alongCell e p q h t a v) (Strict.snd e q) = whiskerLeft (Strict.snd e p) a := rfl
theorem along_comp {V : J ⥤ L} (r : V ⋙ q = p) (a : H ⟶ T) (b : T ⟶ V)
    (v : vertical p q h t a) (w : vertical p q t r b) :
    alongCell e p q h t a v ≫ alongCell e p q t r b w =
      alongCell e p q h r (a ≫ b) (fun x => by simp [q.map_comp,v,w]) := by
  ext x
  apply InducedCategory.hom_ext
  apply CategoricalPullback.hom_ext
  · exact Category.id_comp _
  · rfl
theorem along_eq {j : H = T} :
    alongCell e p q h t (eqToHom j) (fun x => by simp [eqToHom_app,eqToHom_map]) =
      eqToHom (show along e p q H h = along e p q T t by subst T; rfl) := by
  subst T
  ext x
  apply InducedCategory.hom_ext
  apply CategoricalPullback.hom_ext <;> rfl
theorem verticalInv (i : H ≅ T) (v : vertical p q h t i.hom) : vertical p q t h i.inv := by
  intro x
  apply (cancel_epi (q.map (i.hom.app x))).mp
  rw [← q.map_comp,i.hom_inv_id_app,q.map_id,v]
  simp
def alongIsoCell (i : H ≅ T) (v : vertical p q h t i.hom) :
    along e p q H h ≅ along e p q T t where
  hom := alongCell e p q h t i.hom v
  inv := alongCell e p q t h i.inv (verticalInv p q h t i v)
  hom_inv_id := by
    ext x
    apply InducedCategory.hom_ext
    apply CategoricalPullback.hom_ext
    · exact Category.id_comp _
    · exact i.hom_inv_id_app x.snd
  inv_hom_id := by
    ext x
    apply InducedCategory.hom_ext
    apply CategoricalPullback.hom_ext
    · exact Category.id_comp _
    · exact i.inv_hom_id_app x.snd
section Fold
universe b w
variable {B : Type b} [Category.{w} B]
variable (Y G : Bᵒᵖ ⥤ Cat.{w,b}) (e : K ⥤ B) (p d : J ⥤ B)
variable {F U : Total Y d ⥤ Total G (𝟭 B)}
variable (h : F ⋙ pr G = tailSource Y p d) (k : U ⋙ pr G = tailSource Y p d)
noncomputable def foldCell (a : F ⟶ U) (v : vertical _ _ h k a) :
    fold Y e p d G F h ⟶ fold Y e p d G U k :=
  whiskerLeft (separate Y e p d) (whiskerRight (alongCell e _ _ h k a v) (unview G e))
noncomputable def foldIsoCell (i : F ≅ U) (v : vertical _ _ h k i.hom) :
    fold Y e p d G F h ≅ fold Y e p d G U k :=
  isoWhiskerLeft (separate Y e p d) (isoWhiskerRight (alongIsoCell e _ _ h k i v) (unview G e))
theorem foldIso_hom (i : F ≅ U) (v : vertical _ _ h k i.hom) :
    (foldIsoCell Y G e p d h k i v).hom = foldCell Y G e p d h k i.hom v := rfl
theorem fold_eq (j : F = U) :
    foldCell Y G e p d h k (eqToHom j) (fun x => by simp [eqToHom_app,eqToHom_map]) =
      eqToHom (show fold Y e p d G F h = fold Y e p d G U k by subst U; rfl) := by
  unfold foldCell
  rw [along_eq]
  subst U
  simp [fold]
end Fold
section Face
set_option maxHeartbeats 1200000
open NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation TripleEvaluation
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B)) (n m k : Nat)
noncomputable def rightFace : stagedRight S Y n m k ⟶ joinLast S Y n m k :=
  whiskerLeft (rebracket S Y n m k) (whiskerRight
    (foldCell Y (out S (out S Y k) m) (power S n).dest (fixed S (m,k)).source (fixed S (m,k)).dest
      (totalOver S Y m k) (groupedOver S Y m k) (eqToHom (BlockCompositor.onMatched S Y m k))
      (verticalEq _ _ (totalOver S Y m k) (groupedOver S Y m k) (BlockCompositor.onMatched S Y m k)))
    (global S (out S (out S Y k) m) n))
theorem rightFace_spec : rightFace S Y n m k = eqToHom (lastFace S Y n m k) := by
  unfold rightFace
  rw [fold_eq]
  ext x
  simp [eqToHom_app,eqToHom_map]
noncomputable abbrev leftFace := whiskerLeft (collapseLast S Y n m k)
  (eqToHom (BlockCompositor.onMatched S (out S Y k) n m))
theorem leftFace_spec : leftFace S Y n m k = eqToHom (firstFace S Y n m k) := by
  ext x; simp [leftFace,eqToHom_app]
/-- The two total fixed-chart cell pastings commute before packed multiplication.
The suffix pasting uses the action on total vertical transformations. -/
theorem square : leftFace S Y n m k ≫ eqToHom (fixedAssociativity S Y n m k) =
    eqToHom (stages S Y n m k) ≫ rightFace S Y n m k := by
  rw [leftFace_spec,rightFace_spec]
  simp
end Face
end ContextualComposition.GrothendieckStep.SuffixCell
