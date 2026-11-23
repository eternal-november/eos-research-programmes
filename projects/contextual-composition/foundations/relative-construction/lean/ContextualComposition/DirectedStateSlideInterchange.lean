module

public import ContextualComposition.DirectedStateUniversal

/-! Two independent state-coordinate slides on a single mixed-fibre process. Both orders are the full expansion of one product-state slide, with the actual weak comparison cells retained. -/

@[expose] public section
namespace ContextualComposition.DirectedStateSlideInterchange

open CategoryTheory DirectedStateBalance
universe u v u' v' w d
variable {S : Type u} [Category.{v} S] (F : Diagram.{v,u,w,d} S)
set_option backward.isDefEq.respectTransparency false

def expand {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair F k i) :
    (insertion F i).obj ((action F (h ≫ g) (𝟙 i)).obj x) ⟶
    (insertion F k).obj ((action F (𝟙 k) (h ≫ g)).obj x) :=
  (insertion F i).map ((preComp F h g).hom.app x) ≫
  (slide F h).app ((action F g (𝟙 i)).obj x) ≫ (insertion F j).map ((middle F h g).hom.app x) ≫
  (slide F g).app ((action F (𝟙 k) h).obj x) ≫ (insertion F k).map ((postComp F h g).inv.app x)

theorem expand_slide {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair F k i) :
    expand F h g x = (slide F (h ≫ g)).app x := ((restrict (𝟭 (Balance F))).comp h g x).symm

def src {i j : S} (h : i ⟶ j) (x : atPair F j i) := (insertion F i).obj ((action F h (𝟙 i)).obj x)
def dst {i j : S} (h : i ⟶ j) (x : atPair F j i) := (insertion F j).obj ((action F (𝟙 j) h).obj x)

theorem refactor {i j k l : S} (f : i ⟶ j) (g : j ⟶ l) (h : i ⟶ k) (m : k ⟶ l)
    (e : f ≫ g = h ≫ m) (x : atPair F l i) :
    expand F f g x = eqToHom (congrArg (src F · x) e) ≫ expand F h m x ≫ eqToHom (congrArg (dst F · x) e.symm) := by
  rw [expand_slide,expand_slide]
  have changeState {s t : i ⟶ l} (eq : s=t) : (slide F s).app x =
      eqToHom (congrArg (src F · x) eq) ≫ (slide F t).app x ≫ eqToHom (congrArg (dst F · x) eq.symm) := by
    cases eq; simp
  exact changeState e

variable {T : Type u'} [Category.{v'} T] (P : Diagram.{max v v',max u u',w,d} (S × T))

abbrev horizontal {i j : S} (h : i ⟶ j) (t : T) : (i,t) ⟶ (j,t) := ⟨h,𝟙 t⟩
abbrev vertical (i : S) {t z : T} (k : t ⟶ z) : (i,t) ⟶ (i,z) := ⟨𝟙 i,k⟩

theorem independent_labels {i j : S} {t z : T} (h : i ⟶ j) (k : t ⟶ z) :
    horizontal h t ≫ vertical j k = vertical i k ≫ horizontal h z :=
  Prod.ext ((Category.comp_id h).trans (Category.id_comp h).symm) ((Category.id_comp k).trans (Category.comp_id k).symm)

theorem coordinate_square {i j : S} {t z : T} (h : i ⟶ j) (k : t ⟶ z) (x : atPair P (j,z) (i,t)) :
    expand P (horizontal h t) (vertical j k) x =
    eqToHom (congrArg (src P · x) (independent_labels h k)) ≫ expand P (vertical i k) (horizontal h z) x ≫
      eqToHom (congrArg (dst P · x) (independent_labels h k).symm) :=
  refactor P _ _ _ _ (independent_labels h k) x

end ContextualComposition.DirectedStateSlideInterchange
