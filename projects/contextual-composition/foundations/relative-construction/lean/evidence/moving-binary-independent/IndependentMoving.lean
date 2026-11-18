import ContextualComposition.MovingFrames
open CategoryTheory CategoryTheory.Functor
open ContextualComposition.GrothendieckStep
open MovingCoordinates
namespace IndependentMoving
universe u v
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split) (Y : WordTrace.Pr (B := B))
theorem retain {x y : X S Y} (f : x ⟶ y) :
   (adjust S Y x).inv ≫ (chart S Y).functor.map ((read S Y).map f) ≫ (adjust S Y y).hom = f := by
  have h := (recover S Y).hom.naturality f
  change (chart S Y).functor.map ((read S Y).map f) ≫ (adjust S Y y).hom = (adjust S Y x).hom ≫ f at h
  rw [h, Iso.inv_hom_id_assoc]
theorem movingSeparation {x y : X S Y} {f g : x ⟶ y}
    (h : (base S Y).map f ≠ (base S Y).map g) : (read S Y).map f ≠ (read S Y).map g := by
  intro k
  apply h; rw [← retain S Y f, ← retain S Y g,k]
theorem parallelSeparation {x y : X S Y} {f g : x ⟶ y} (h : f ≠ g) :
    (read S Y).map f ≠ (read S Y).map g := by
  intro k
  apply h; rw [← retain S Y f, ← retain S Y g,k]
theorem uniqueOnChosenEndpoints (s : MovingCell.leftTotal S Y ⟶ MovingCell.rightTotal S Y)
    (h : ∀ x, s.app x = (MovingCell.I S Y x).map ((BlockCompositor.compositor S Y (MovingCell.A S Y x)).hom.app (point S Y x))) :
    s = (MovingCell.cell S Y).hom := by
  apply NatTrans.ext; funext x; exact (h x).trans (MovingCell.component S Y x).symm
theorem componentVertical (x : X S Y) :
    (FibreValue.proj (ChartRealization.twice S Y)).map ((MovingCell.cell S Y).hom.app x) = 𝟙 (MovingCell.A S Y x) := by
  rw [MovingCell.component]; rfl
end IndependentMoving
