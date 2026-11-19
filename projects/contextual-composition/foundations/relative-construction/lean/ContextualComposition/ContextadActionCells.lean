module
public import ContextualComposition.ContextadWeakAction
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadWeakAction
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks BoundaryPaste SuffixCell
set_option backward.isDefEq.respectTransparency false
universe b w k l
variable {B : Type b} [Category.{w} B] {K : Type k} [Category.{l} K]
variable {Y Z : Bᵒᵖ ⥤ Cat.{w,b}} (e : K ⥤ B)
variable {F G H : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)} (f : F ⋙ pr Z = pr Y) (g : G ⋙ pr Z = pr Y) (h : H ⋙ pr Z = pr Y)
variable (a : F ⟶ G) (v : vertical (pr Y) (pr Z) f g a)
noncomputable def actionCell : action e F f ⟶ action e G g :=
  whiskerLeft (view Y e) (whiskerRight (alongCell e (pr Y) (pr Z) f g a v) (unview Z e))
noncomputable def actionIso (i : F ≅ G) (w : vertical (pr Y) (pr Z) f g i.hom) :
    action e F f ≅ action e G g :=
  isoWhiskerLeft (view Y e) (isoWhiskerRight (alongIsoCell e (pr Y) (pr Z) f g i w) (unview Z e))
theorem actionIso_hom (i : F ≅ G) (w : vertical (pr Y) (pr Z) f g i.hom) :
    (actionIso e f g i w).hom = actionCell e f g i.hom w := rfl
theorem actionCell_id :
    actionCell e f f (𝟙 F) (fun x => by simp) = 𝟙 _ := by
  unfold actionCell
  have t : alongCell e (pr Y) (pr Z) f f (𝟙 F) (fun _ => by simp) = 𝟙 _ :=
    along_eq e (pr Y) (pr Z) f f (j := rfl)
  rw [t]; simp [action]
theorem actionCell_comp (b : G ⟶ H) (w : vertical (pr Y) (pr Z) g h b) :
    actionCell e f g a v ≫ actionCell e g h b w =
      actionCell e f h (a ≫ b) (fun x => by simp [Functor.map_comp,v,w]) := by
  unfold actionCell
  rw [← whiskerLeft_comp,← whiskerRight_comp,along_comp]
end ContextualComposition.GrothendieckStep.ContextadWeakAction
