module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat

/-! Directed contraction of a Cat-valued state diagram. Only native arrows and forward state slides generate paths. Composition uses the pseudofunctor's actual comparison cells. -/

@[expose] public section
namespace ContextualComposition.DirectedStateBalance

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u w d
variable {S : Type u} [Category.{v} S]
-- The fibres retain independently chosen object and morphism universes.
set_option linter.checkUnivs false in
abbrev Diagram (S : Type u) [Category.{v} S] := LocallyDiscrete (Sᵒᵖ × S) ⥤ᵖ Cat.{w,d}
variable (F : Diagram.{v,u,w,d} S)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev atPair (i j : S) := F.obj ⟨(op i,j)⟩
def pairMap {i i' j j' : S} (h : i' ⟶ i) (k : j ⟶ j') : (op i,j) ⟶ (op i',j') := ⟨h.op,k⟩
abbrev action {i i' j j' : S} (h : i' ⟶ i) (k : j ⟶ j') : atPair F i j ⥤ atPair F i' j' :=
  (F.map (pairMap h k).toLoc).toFunctor

def actionComp {i i' i'' j j' j'' : S} (h : i' ⟶ i) (h' : i'' ⟶ i') (k : j ⟶ j') (k' : j' ⟶ j'') :
    action F (h' ≫ h) (k ≫ k') ≅ action F h k ⋙ action F h' k' :=
  Cat.Hom.toNatIso (F.mapComp (pairMap h k).toLoc (pairMap h' k').toLoc)

def preComp {i j k : S} (h : i ⟶ j) (g : j ⟶ k) :
    action F (h ≫ g) (𝟙 i) ≅ action F g (𝟙 i) ⋙ action F h (𝟙 i) :=
  eqToIso (congrArg (action F (h ≫ g)) (Category.id_comp (𝟙 i)).symm) ≪≫ actionComp F g h _ _

def postComp {i j k : S} (h : i ⟶ j) (g : j ⟶ k) :
    action F (𝟙 k) (h ≫ g) ≅ action F (𝟙 k) h ⋙ action F (𝟙 k) g :=
  eqToIso (congrArg (fun t => action F t (h ≫ g)) (Category.id_comp (𝟙 k)).symm) ≪≫ actionComp F _ _ h g

/-- Both presentations of the middle state act through the same mixed arrow. -/
def middle {i j k : S} (h : i ⟶ j) (g : j ⟶ k) :
    action F g (𝟙 i) ⋙ action F (𝟙 j) h ≅ action F (𝟙 k) h ⋙ action F g (𝟙 j) :=
  (actionComp F g (𝟙 j) (𝟙 i) h).symm ≪≫
  eqToIso (by simp) ≪≫ actionComp F (𝟙 k) g h (𝟙 j)

structure Vertex where
  state : S
  val : atPair F state state

inductive Edge : Vertex F → Vertex F → Type (max u v w d)
  | native {i : S} {x y : atPair F i i} (a : x ⟶ y) : Edge ⟨i,x⟩ ⟨i,y⟩
  | slide {i j : S} (h : i ⟶ j) (x : atPair F j i) :
    Edge ⟨i,(action F h (𝟙 i)).obj x⟩ ⟨j,(action F (𝟙 j) h).obj x⟩

instance : Quiver (Vertex F) := ⟨Edge F⟩
abbrev PathCat := Paths (Vertex F)
def generator {x y : Vertex F} (t : Edge F x y) :
    (Paths.of (Vertex F)).obj x ⟶ (Paths.of _).obj y := (Paths.of _).map t
abbrev nativePath {i : S} {x y : atPair F i i} (a : x ⟶ y) := generator F (.native a)
abbrev slidePath {i j : S} (h : i ⟶ j) (x : atPair F j i) := generator F (.slide h x)

inductive Relation : HomRel (PathCat F)
  | nativeId {i : S} (x : atPair F i i) : Relation (nativePath F (𝟙 x)) (𝟙 _)
  | nativeComp {i : S} {x y z : atPair F i i} (a : x ⟶ y) (b : y ⟶ z) :
    Relation (nativePath F a ≫ nativePath F b) (nativePath F (a ≫ b))
  | natural {i j : S} (h : i ⟶ j) {x y : atPair F j i} (a : x ⟶ y) :
    Relation (nativePath F ((action F h (𝟙 i)).map a) ≫ slidePath F h y)
      (slidePath F h x ≫ nativePath F ((action F (𝟙 j) h).map a))
  | unit {i : S} (x : atPair F i i) : Relation (slidePath F (𝟙 i) x) (𝟙 _)
  | comp {i j k : S} (h : i ⟶ j) (g : j ⟶ k) (x : atPair F k i) :
    Relation (slidePath F (h ≫ g) x)
      (nativePath F ((preComp F h g).hom.app x) ≫ slidePath F h ((action F g (𝟙 i)).obj x) ≫
       nativePath F ((middle F h g).hom.app x) ≫ slidePath F g ((action F (𝟙 k) h).obj x) ≫
       nativePath F ((postComp F h g).inv.app x))

abbrev Balance := CategoryTheory.Quotient (Relation F)
abbrev Q := CategoryTheory.Quotient.functor (Relation F)

def insertion (i : S) : atPair F i i ⥤ Balance F where
  obj x := (Q F).obj ((Paths.of _).obj ⟨i,x⟩)
  map a := (Q F).map (nativePath F a)
  map_id x := (CategoryTheory.Quotient.sound _ (Relation.nativeId x)).trans ((Q F).map_id _)
  map_comp a b := (CategoryTheory.Quotient.sound _ (Relation.nativeComp a b)).symm.trans ((Q F).map_comp _ _)

def slide {i j : S} (h : i ⟶ j) :
    action F h (𝟙 i) ⋙ insertion F i ⟶ action F (𝟙 j) h ⋙ insertion F j where
  app x := (Q F).map (slidePath F h x)
  naturality _ _ a := ((Q F).map_comp _ _).symm.trans
    ((CategoryTheory.Quotient.sound _ (Relation.natural h a)).trans ((Q F).map_comp _ _))

abbrev strict (G : Sᵒᵖ × S ⥤ Cat.{w,d}) : Diagram S := G.toPseudofunctor'

end ContextualComposition.DirectedStateBalance
