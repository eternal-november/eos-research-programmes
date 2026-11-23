module
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG
variable {B : Type u} [Category.{v} B]
variable (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})
set_option backward.isDefEq.respectTransparency false

structure Vertex where
  mid : B
  first : F.obj ⟨mid⟩
  second : G.obj ⟨op mid⟩

abbrev forward {i j : B} (u : i ⟶ j) := (F.map u.toLoc).toFunctor
abbrev backward {i j : B} (u : i ⟶ j) := (G.map u.op.toLoc).toFunctor

/-- An ordinary product arrow and the two directions of a pure middle balance generate the path category. -/
inductive Edge : Vertex F G → Vertex F G → Type (max u v uF vF uG vG)
  | native {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (a : x ⟶ x') (b : y ⟶ y') : Edge ⟨i,x,y⟩ ⟨i,x',y'⟩
  | balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) : Edge ⟨i,x,(backward G u).obj y⟩ ⟨j,(forward F u).obj x,y⟩
  | unbalance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) : Edge ⟨j,(forward F u).obj x,y⟩ ⟨i,x,(backward G u).obj y⟩

instance vertexQuiver : Quiver (Vertex F G) := ⟨Edge F G⟩
abbrev paths := Paths (Vertex F G)
def generator {x y : Vertex F G} (a : Edge F G x y) :
    (Paths.of (Vertex F G)).obj x ⟶ (Paths.of (Vertex F G)).obj y := (Paths.of _).map a

abbrev nativePath {i : B} {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op i⟩} (a : x ⟶ x') (b : y ⟶ y') := generator F G (Edge.native a b)
abbrev balancePath {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) := generator F G (Edge.balance u x y)
abbrev inverseBalancePath {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) := generator F G (Edge.unbalance u x y)

/-- The last two relations insert the given unit and composition constraints on both sides of the shared variable. -/
inductive Relations : HomRel (paths F G)
  | nativeId {i : B} (x : F.obj ⟨i⟩) (y : G.obj ⟨op i⟩) : Relations (nativePath F G (𝟙 x) (𝟙 y)) (𝟙 _)
  | nativeComp {i : B} {x y z : F.obj ⟨i⟩} {r s t : G.obj ⟨op i⟩}
      (a : x ⟶ y) (b : r ⟶ s) (c : y ⟶ z) (d : s ⟶ t) : Relations (nativePath F G a b ≫ nativePath F G c d) (nativePath F G (a ≫ c) (b ≫ d))
  | balInv {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) : Relations (balancePath F G u x y ≫ inverseBalancePath F G u x y) (𝟙 _)
  | invBal {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) : Relations (inverseBalancePath F G u x y ≫ balancePath F G u x y) (𝟙 _)
  | natural {i j : B} (u : i ⟶ j) {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op j⟩} (a : x ⟶ x') (b : y ⟶ y') :
      Relations (nativePath F G a ((backward G u).map b) ≫ balancePath F G u x' y') (balancePath F G u x y ≫ nativePath F G ((forward F u).map a) b)
  | unit {i : B} (x : F.obj ⟨i⟩) (y : G.obj ⟨op i⟩) :
      Relations (balancePath F G (𝟙 i) x y) (nativePath F G ((F.mapId ⟨i⟩).inv.toNatTrans.app x) ((G.mapId ⟨op i⟩).hom.toNatTrans.app y))
  | comp {i j k : B} (u : i ⟶ j) (v : j ⟶ k) (x : F.obj ⟨i⟩) (y : G.obj ⟨op k⟩) :
      Relations (balancePath F G (u ≫ v) x y)
        (nativePath F G (𝟙 x) ((G.mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app y) ≫ balancePath F G u x ((backward G v).obj y) ≫
          balancePath F G v ((forward F u).obj x) y ≫ nativePath F G ((F.mapComp u.toLoc v.toLoc).inv.toNatTrans.app x) (𝟙 y))

abbrev Tensor := CategoryTheory.Quotient (Relations F G)
abbrev quotient := CategoryTheory.Quotient.functor (Relations F G)

/-- Embedding the product-category generators defines an ordinary functor at each middle object. -/
def insertion (i : B) : (F.obj ⟨i⟩ × G.obj ⟨op i⟩) ⥤ Tensor F G where
  obj p := (quotient F G).obj ((Paths.of (Vertex F G)).obj ⟨i,p.1,p.2⟩)
  map f := (quotient F G).map (nativePath F G f.1 f.2)
  map_id p := (CategoryTheory.Quotient.sound _ (Relations.nativeId p.1 p.2)).trans ((quotient F G).map_id _)
  map_comp f g := (CategoryTheory.Quotient.sound _ (Relations.nativeComp f.1 f.2 g.1 g.2)).symm.trans ((quotient F G).map_comp _ _)

def balancing {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (insertion F G i).obj (x,(backward G u).obj y) ≅ (insertion F G j).obj ((forward F u).obj x,y) where
  hom := (quotient F G).map (balancePath F G u x y)
  inv := (quotient F G).map (inverseBalancePath F G u x y)
  hom_inv_id := ((quotient F G).map_comp _ _).symm.trans ((CategoryTheory.Quotient.sound _ (Relations.balInv u x y)).trans ((quotient F G).map_id _))
  inv_hom_id := ((quotient F G).map_comp _ _).symm.trans ((CategoryTheory.Quotient.sound _ (Relations.invBal u x y)).trans ((quotient F G).map_id _))

end ContextualComposition.RelativeTensor
