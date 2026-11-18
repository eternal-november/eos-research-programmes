module
public import ContextualComposition.EndpointValues
@[expose] public section
namespace ContextualComposition.GrothendieckStep.WholeEvaluator
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks NativeBlocks.Nested NativePacked BlockEvaluation CoproductSpan
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
abbrev one := (PackedFree.free S).obj Y
abbrev charts := Distribute.gather Y (fun n => (power S n).dest)
def unpack (x : Total Y (whole S).dest) : Σ n, Total Y (power S n).dest :=
  ⟨(grade _ _ x).1, pair Y _ (grade _ _ x).2 (payload _ _ x)⟩
def split : Total Y (whole S).dest ⥤ Σ n, Total Y (power S n).dest where
  obj := unpack S Y
  map {x y} f := Distribute.splitHom Y (fun n => (power S n).dest) (x:=unpack S Y x) (y:=unpack S Y y) f
  map_id x := (charts S Y).map_injective (by rw [Distribute.gather_split,Functor.map_id]; rfl)
  map_comp f g := (charts S Y).map_injective (by rw [Distribute.gather_split,Functor.map_comp,Distribute.gather_split,Distribute.gather_split])
theorem onTag (n : Nat) : Lift.total (tag (power S) n) Y ⋙ split S Y = Sigma.incl (C := fun n => Total Y (power S n).dest) n := by
  fapply Functor.ext
  · intro x; rfl
  · intro x y f; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; simp only [Category.id_comp,Category.comp_id]; exact Distribute.split_gather Y (fun n => (power S n).dest) ((Sigma.incl (C := fun n => Total Y (power S n).dest) n).map f)
abbrev branch (n : Nat) := global S Y n ⋙ ChainPayload.fibreMap (PackedFree.inc S Y n) (𝟭 B)
def evaluate := split S Y ⋙ Sigma.desc (branch S Y)
theorem tagged (n : Nat) : Lift.total (tag (power S) n) Y ⋙ evaluate S Y = branch S Y n :=
  (congrArg (· ⋙ Sigma.desc (branch S Y)) (onTag S Y n)).trans rfl
theorem over : evaluate S Y ⋙ gradeProjection = gradeProjection ⋙ (whole S).source := by
  have h : Sigma.desc (branch S Y) ⋙ gradeProjection = charts S Y ⋙ gradeProjection ⋙ (whole S).source := by
    apply PackedFree.sigma_ext; intro n
    have z : Sigma.incl (C := fun n => Total Y (power S n).dest) n ⋙ charts S Y = Lift.total (tag (power S) n) Y := by apply Functor.ext (fun _ => rfl)
    have b : Sigma.incl (C := fun n => Total Y (power S n).dest) n ⋙ charts S Y ⋙ NativeCleavage.FibreTotal.projection Y (whole S).dest (whole S).source = NativeCleavage.FibreTotal.projection Y (power S n).dest (power S n).source :=
      by rw [← Functor.assoc, z]; exact Lift.over (tag (power S) n) Y
    exact (globalOver S Y n).trans b.symm
  have k : split S Y ⋙ charts S Y = 𝟭 _ := by
    fapply Functor.ext
    · intro x; rfl
    · intro x y f; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; simp only [Category.id_comp,Category.comp_id]; exact Distribute.gather_split Y _ _
  exact (congrArg (split S Y ⋙ ·) h).trans (congrArg (· ⋙ gradeProjection ⋙ (whole S).source) k)
end ContextualComposition.GrothendieckStep.WholeEvaluator
