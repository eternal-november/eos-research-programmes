module

public import ContextualComposition.DirectedStateDiagramMap

/-! Modifications of natural transformations of diagrams act on their directed contractions. The extra square used at a slide is component naturality at the off-diagonal argument. -/

@[expose] public section
namespace ContextualComposition.DirectedStateModifications

open CategoryTheory Opposite DirectedStateBalance DirectedStateDiagramMap DirectedStateNativeFaithfulness DirectedStateIntertwiners
universe v u w d
variable {S : Type u} [Category.{v} S]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fromGenerators {F : Diagram.{v,u,w,d} S} {D : Type*} [Category* D] {P Q : Balance F ⥤ D}
    (atObj : ∀ i (x : atPair F i i), P.obj ((insertion F i).obj x) ⟶ Q.obj ((insertion F i).obj x))
    (hn : ∀ {i} {x y : atPair F i i} (f : x ⟶ y),
      P.map ((insertion F i).map f) ≫ atObj i y = atObj i x ≫ Q.map ((insertion F i).map f))
    (hs : ∀ {i j} (h : i ⟶ j) (x : atPair F j i),
      P.map ((slide F h).app x) ≫ atObj j _ = atObj i _ ≫ Q.map ((slide F h).app x)) : P ⟶ Q := by
  apply CategoryTheory.Quotient.natTransLift (Relation F)
  refine ⟨fun x => atObj x.state x.val,?_⟩
  intro x y p
  induction p with
  | nil =>
    change P.map ((DirectedStateBalance.Q F).map (𝟙 _)) ≫ _ = _ ≫ Q.map ((DirectedStateBalance.Q F).map (𝟙 _))
    simp only [Functor.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  | @cons i j p e ih =>
    have edge : P.map ((DirectedStateBalance.Q F).map (generator F e)) ≫ atObj j.state j.val =
        atObj i.state i.val ≫ Q.map ((DirectedStateBalance.Q F).map (generator F e)) := by
      cases e with | native f => exact hn f | slide h z => exact hs h z
    change P.map ((DirectedStateBalance.Q F).map (p ≫ generator F e)) ≫ _ = _ ≫ Q.map ((DirectedStateBalance.Q F).map (p ≫ generator F e))
    simp only [Functor.map_comp,Category.assoc,edge]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Q.map ((DirectedStateBalance.Q F).map (generator F e))) ih).trans (Category.assoc _ _ _))

variable {G H : Sᵒᵖ × S ⥤ Cat.{w,d}} {n m : G ⟶ H}

structure Modification (n m : G ⟶ H) where
  cell (i j : S) : component n i j ⟶ component m i j
  natural {i i' j j' : S} (h : i' ⟶ i) (k : j ⟶ j') (x : atPair (strict G) i j) :
    Conjugate ((cell i' j').app ((action (strict G) h k).obj x))
      ((action (strict H) h k).map ((cell i j).app x))

def descend (p : Modification n m) : map n ⟶ map m := by
  apply fromGenerators (fun i x => (insertion (strict H) i).map ((p.cell i i).app x))
  · intro i x y f
    rw [map_native,map_native,← Functor.map_comp,← Functor.map_comp,(p.cell i i).naturality f]
  · intro i j h x
    rw [map_slide,map_slide]
    have a := comp_conjugate (move_conjugate n h x)
      (map_conjugate (insertion (strict H) j) (p.natural (𝟙 j) h x))
    have b := comp_conjugate (map_conjugate (insertion (strict H) i) (p.natural h (𝟙 i) x)) (move_conjugate m h x)
    have e := (slide (strict H) h).naturality ((p.cell j i).app x)
    exact (a.trans (e ▸ b.symm)).eq

theorem descend_app (p : Modification n m) (i : S) (x : atPair (strict G) i i) :
    (descend p).app ((insertion _ i).obj x) = (insertion (strict H) i).map ((p.cell i i).app x) := rfl

theorem insertion_natural (n : G ⟶ H) (i : S) :
    insertion (strict G) i ⋙ map n = component n i i ⋙ insertion (strict H) i := by
  apply Functor.hext (F := insertion (strict G) i ⋙ map n) (G := component n i i ⋙ insertion (strict H) i) (fun _ => rfl)
  exact fun _ _ f => heq_of_eq (map_native n f)

theorem applied_slide {F : Diagram.{v,u,w,d} S} {D : Type*} [Category* D]
    (c : DirectedStateBalance.Cocone F D) {i j : S} (h : i ⟶ j) (z : atPair F j i) :
    c.descend.map ((slide F h).app z) = (c.bal h).app z := c.descend_generator (Edge.slide (F:=F) h z)

end ContextualComposition.DirectedStateModifications
