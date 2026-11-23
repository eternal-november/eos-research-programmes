module
public import ContextualComposition.RelativeTensor

@[expose] public section
namespace ContextualComposition.RelativeTensor
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF vG uG vD uD
variable {B : Type u} [Category.{v} B]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}
variable {D : Type uD} [Category.{vD} D]
set_option backward.isDefEq.respectTransparency false

abbrev productMap {X Y : Type*} [Category* X] [Category* Y] {x x' : X} {y y' : Y}
    (a : x ⟶ x') (b : y ⟶ y') : (x,y) ⟶ (x',y') := ⟨a,b⟩

/-- A pseudobalanced cocone is given on the product categories themselves. Its laws refer to the supplied weak actions of both factors. -/
structure Cocone (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}) (D : Type uD) [Category.{vD} D] where
  fiber : (i : B) → (F.obj ⟨i⟩ × G.obj ⟨op i⟩) ⥤ D
  bal {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : G.obj ⟨op j⟩) :
    (fiber i).obj (x,(backward G u).obj y) ≅ (fiber j).obj ((forward F u).obj x,y)
  natural {i j : B} (u : i ⟶ j) {x x' : F.obj ⟨i⟩} {y y' : G.obj ⟨op j⟩} (a : x ⟶ x') (b : y ⟶ y') :
    (fiber i).map ⟨a,(backward G u).map b⟩ ≫ (bal u x' y').hom =
      (bal u x y).hom ≫ (fiber j).map ⟨(forward F u).map a,b⟩
  unit {i : B} (x : F.obj ⟨i⟩) (y : G.obj ⟨op i⟩) :
    (bal (𝟙 i) x y).hom = (fiber i).map ⟨(F.mapId ⟨i⟩).inv.toNatTrans.app x,(G.mapId ⟨op i⟩).hom.toNatTrans.app y⟩
  comp {i j k : B} (u : i ⟶ j) (v : j ⟶ k) (x : F.obj ⟨i⟩) (y : G.obj ⟨op k⟩) :
    (bal (u ≫ v) x y).hom =
      (fiber i).map ⟨𝟙 x,(G.mapComp v.op.toLoc u.op.toLoc).hom.toNatTrans.app y⟩ ≫
      (bal u x ((backward G v).obj y)).hom ≫ (bal v ((forward F u).obj x) y).hom ≫
      (fiber k).map (productMap ((F.mapComp u.toLoc v.toLoc).inv.toNatTrans.app x) (𝟙 y))

def restrict (H : Tensor F G ⥤ D) : Cocone F G D where
  fiber i := insertion F G i ⋙ H
  bal u x y := H.mapIso (balancing F G u x y)
  natural := by
    intro i j u x x' y y' a b
    have h := congrArg H.map (CategoryTheory.Quotient.sound (Relations F G) (Relations.natural u a b))
    simp only [Functor.map_comp] at h
    exact h
  unit x y := congrArg H.map (CategoryTheory.Quotient.sound (Relations F G) (Relations.unit x y))
  comp u v x y := by
    have h := congrArg H.map (CategoryTheory.Quotient.sound (Relations F G) (Relations.comp u v x y))
    simp only [Functor.map_comp] at h
    exact h

namespace Cocone
variable (S : Cocone F G D)

def graph : Vertex F G ⥤q D where
  obj p := (S.fiber p.mid).obj (p.first,p.second)
  map f := match f with
    | .native a b => (S.fiber _).map ⟨a,b⟩
    | .balance u x y => (S.bal u x y).hom
    | .unbalance u x y => (S.bal u x y).inv

theorem map_generator {x y : Vertex F G} (f : Edge F G x y) :
    (Paths.lift S.graph).map (generator F G f) = S.graph.map f := Paths.lift_toPath S.graph (show x ⟶ y from f)

theorem respects {x y : paths F G} {a b : x ⟶ y} (h : Relations F G a b) :
    (Paths.lift S.graph).map a = (Paths.lift S.graph).map b := by
  cases h with
  | nativeId x y =>
    rw [map_generator, Functor.map_id]
    exact (S.fiber _).map_id (x,y)
  | nativeComp a b c d =>
    rw [Functor.map_comp, map_generator, map_generator, map_generator]
    exact ((S.fiber _).map_comp (productMap a b) (productMap c d)).symm
  | balInv u x y =>
    rw [Functor.map_comp, map_generator, map_generator, Functor.map_id]; exact (S.bal u x y).hom_inv_id
  | invBal u x y =>
    rw [Functor.map_comp, map_generator, map_generator, Functor.map_id]; exact (S.bal u x y).inv_hom_id
  | natural u a b =>
    simp only [Functor.map_comp, nativePath, balancePath, map_generator]; exact S.natural u a b
  | unit x y => rw [map_generator, map_generator]; exact S.unit x y
  | comp u v x y =>
    simp only [Functor.map_comp, nativePath, balancePath, map_generator]; exact S.comp u v x y

/-- The induced functor evaluates finite paths and descends through precisely the generating equations. -/
def extend : Tensor F G ⥤ D :=
  CategoryTheory.Quotient.lift (Relations F G) (Paths.lift S.graph) (fun _ _ _ _ h => S.respects h)

theorem extend_generator {x y : Vertex F G} (f : Edge F G x y) :
    S.extend.map ((quotient F G).map (generator F G f)) = S.graph.map f := S.map_generator f

end Cocone

theorem extend_restrict (H : Tensor F G ⥤ D) : (restrict H).extend = H := by
  apply CategoryTheory.Quotient.lift_unique'
  unfold Cocone.extend
  rw [CategoryTheory.Quotient.lift_spec]
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro x; rfl
  · intro x y f
    cases f <;> rfl

end ContextualComposition.RelativeTensor
