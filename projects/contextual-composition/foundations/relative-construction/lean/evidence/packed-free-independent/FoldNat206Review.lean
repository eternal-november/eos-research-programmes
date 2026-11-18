import ContextualComposition.PackedFree
open CategoryTheory ContextualComposition.GrothendieckStep PackedFree
namespace FoldNat206
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
  {X Y Z W : Bᵒᵖ ⥤ Cat.{max u v,u}}
-- Naturality of the free extension in a genuine algebra morphism.
example (a : (step S).obj Z ⟶ Z) (c : (step S).obj W ⟶ W) (h : Z ⟶ W) (hh : HomLaw S a c h)
    (f : Y ⟶ Z) : fold S a f ≫ h = fold S c (f ≫ h) := by
  apply hom_ext S c (hom_comp S (fold_hom S a f) hh) (fold_hom S c (f ≫ h))
  rw [← Category.assoc, inc_fold, inc_fold]; rfl
-- Naturality in the source generator uses the existing endofunctor's actual arrow map.
example (q : X ⟶ Y) (f : Y ⟶ Z) (a : (step S).obj Z ⟶ Z) :
    (free S).map q ≫ fold S a f = fold S a (q ≫ f) := by
  apply hom_ext S a (hom_comp S (map_hom S q) (fold_hom S a f)) (fold_hom S a (q ≫ f))
  rw [← Category.assoc,inc_map,Category.assoc,inc_fold,inc_fold];rfl
end FoldNat206
