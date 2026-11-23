module

public import ContextualComposition.DirectedStateUniversal
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! Single-state-map normalization using the chosen adjunction. Formula (N) consists of an actual native unit, a forward slide and a native target cell. Its counit specialization is the original slide. -/

@[expose] public section
namespace ContextualComposition.DirectedStateAdjointableCell

open CategoryTheory Opposite DirectedStateBalance
universe u v w d
variable {S : Type u} [Category.{v} S] {F : Diagram.{v,u,w,d} S} {i j : S} (h : i ⟶ j)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : atPair F i i ⥤ atPair F j i} (adj : A ⊣ action F h (𝟙 i))

/-- The target transport of a source process once its chosen left action adjoint is installed. -/
abbrev transport (x : atPair F i i) := (action F (𝟙 j) h).obj (A.obj x)

def normal {x : atPair F i i} {y : atPair F j j} (α : transport (A:=A) h x ⟶ y) :
    (insertion F i).obj x ⟶ (insertion F j).obj y :=
  (insertion F i).map (adj.unit.app x) ≫ (slide F h).app (A.obj x) ≫ (insertion F j).map α

theorem normal_post {x : atPair F i i} {y z : atPair F j j} (α : transport (A:=A) h x ⟶ y) (β : y ⟶ z) :
    normal h adj (α ≫ β) = normal h adj α ≫ (insertion F j).map β := by
  simp only [normal,Functor.map_comp,Category.assoc]

theorem normal_pre {x x' : atPair F i i} {y : atPair F j j} (f : x ⟶ x') (α : transport (A:=A) h x' ⟶ y) :
    (insertion F i).map f ≫ normal h adj α =
    normal h adj ((action F (𝟙 j) h).map (A.map f) ≫ α) := by
  have e : f ≫ adj.unit.app x' = adj.unit.app x ≫ (action F h (𝟙 i)).map (A.map f) := adj.unit.naturality f
  have s := (slide F h).naturality (A.map f)
  change (insertion F i).map ((action F h (𝟙 i)).map (A.map f)) ≫ _ =
    _ ≫ (insertion F j).map ((action F (𝟙 j) h).map (A.map f)) at s
  simp only [normal,Functor.map_comp]
  rw [← Category.assoc,← Functor.map_comp,e,Functor.map_comp,Category.assoc,← Category.assoc _ ((slide F h).app _),s,Category.assoc]

/-- Moving the counit past a directed slide uses naturality and the triangle identity. No inverse to the slide occurs. -/
theorem normal_slide (y : atPair F j i) :
    normal h adj ((action F (𝟙 j) h).map (adj.counit.app y)) = (slide F h).app y := by
  have s := (slide F h).naturality (adj.counit.app y)
  change (insertion F i).map ((action F h (𝟙 i)).map (adj.counit.app y)) ≫ (slide F h).app y =
    (slide F h).app (A.obj ((action F h (𝟙 i)).obj y)) ≫ (insertion F j).map ((action F (𝟙 j) h).map (adj.counit.app y)) at s
  unfold normal
  rw [← s,← Category.assoc,← Functor.map_comp,adj.right_triangle_components,Functor.map_id,Category.id_comp]

variable {B : atPair F i j ⥤ atPair F j j} (outAdj : B ⊣ action F h (𝟙 j))

/-- The mixed square at h, assembled from the actual two pseudofunctor compositors. -/
def commute : action F h (𝟙 i) ⋙ action F (𝟙 i) h ≅ action F (𝟙 j) h ⋙ action F h (𝟙 j) :=
  (actionComp F h (𝟙 i) (𝟙 i) h).symm ≪≫ eqToIso (by simp) ≪≫ actionComp F (𝟙 j) h h (𝟙 j)

def mateUnit (x : atPair F i i) :
    (action F (𝟙 i) h).obj x ⟶ (action F h (𝟙 j)).obj (transport (A:=A) h x) :=
  (action F (𝟙 i) h).map (adj.unit.app x) ≫ (commute (F := F) h).hom.app (A.obj x)

/-- The canonical mate of interchange. Arbitrary unrelated adjunctions on two fibres need not make this mate invertible. -/
def mateComparison (x : atPair F i i) : B.obj ((action F (𝟙 i) h).obj x) ⟶ transport (A:=A) h x :=
  (outAdj.homEquiv _ _).symm (mateUnit h adj x)

/-- Under invertibility of the canonical mate, actual Grothendieck fibre maps and actual state intertwiners correspond. -/
noncomputable def mateEquiv (x : atPair F i i) (y : atPair F j j) [IsIso (mateComparison h adj outAdj x)] :
    (transport (A:=A) h x ⟶ y) ≃ ((action F (𝟙 i) h).obj x ⟶ (action F h (𝟙 j)).obj y) where
  toFun α := outAdj.homEquiv _ _ (mateComparison h adj outAdj x ≫ α)
  invFun β := inv (mateComparison h adj outAdj x) ≫ (outAdj.homEquiv _ _).symm β
  left_inv _ := by simp
  right_inv _ := by simp

end ContextualComposition.DirectedStateAdjointableCell
