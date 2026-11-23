module
public import ContextualComposition.RelativeTensorUniversal
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section
namespace ContextualComposition.RelativeTensor.LeftUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vG uG
variable {B : Type u} [Category.{v} B]
variable (a : B) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})
set_option backward.isDefEq.respectTransparency false
attribute [local simp] PrelaxFunctor.map₂_eqToHom

/-- The identity module at input a is the discrete covariant representable on arrows out of a. -/
abbrev represented := (coyoneda.obj (op a) ⋙ typeToCat).toPseudofunctor'

def evalFiber (i : B) : (Discrete (a ⟶ i) × G.obj ⟨op i⟩) ⥤ G.obj ⟨op a⟩ where
  obj s := (backward G s.1.as).obj s.2
  map {s t} f := (backward G s.1.as).map f.2 ≫ eqToHom (by rw [Discrete.eq_of_hom f.1])
  map_id s := by simp
  map_comp {x y z} f g := by
    obtain ⟨⟨x⟩,p⟩ := x
    obtain ⟨⟨y⟩,q⟩ := y
    obtain ⟨⟨z⟩,r⟩ := z
    obtain rfl : x = y := Discrete.eq_of_hom f.1
    obtain rfl : x = z := Discrete.eq_of_hom g.1
    simp

def evalBalance {i j : B} (u : i ⟶ j) (x : Discrete (a ⟶ i)) (y : G.obj ⟨op j⟩) :
    (evalFiber a G i).obj (x,(backward G u).obj y) ≅
      (evalFiber a G j).obj ((forward (represented a) u).obj x,y) :=
  (Cat.Hom.toNatIso (G.mapComp u.op.toLoc x.as.op.toLoc)).symm.app y

def evaluationCocone : Cocone (represented a) G (G.obj ⟨op a⟩) where
  fiber := evalFiber a G
  bal := evalBalance a G
  natural := by
    intro i j u x x' y y' p q
    obtain rfl : x = x' := Discrete.ext (Discrete.eq_of_hom p)
    change ((backward G x.as).map ((backward G u).map q) ≫ eqToHom _) ≫
      (G.mapComp u.op.toLoc x.as.op.toLoc).inv.toNatTrans.app y' =
      (G.mapComp u.op.toLoc x.as.op.toLoc).inv.toNatTrans.app y ≫ (backward G (x.as ≫ u)).map q ≫ eqToHom _
    erw [eqToHom_refl, Category.comp_id, eqToHom_refl, Category.comp_id]
    exact (G.mapComp u.op.toLoc x.as.op.toLoc).inv.toNatTrans.naturality q
  unit x y := by
    change (G.mapComp (𝟙 _) x.as.op.toLoc).inv.toNatTrans.app y =
      (backward G x.as).map ((G.mapId _).hom.toNatTrans.app y) ≫ eqToHom _
    simp [G.mapComp_id_left_inv_app, Bicategory.Strict.leftUnitor_eqToIso]
  comp u v x y := by
    let p := x.as.op.toLoc
    let i := (backward G x.as).mapIso ((Cat.Hom.toNatIso (G.mapComp v.op.toLoc u.op.toLoc)).app y)
    have h := G.mapComp_assoc_left_inv_app v.op.toLoc u.op.toLoc p y
    simp only [Bicategory.Strict.associator_eqToIso, eqToIso.inv, PrelaxFunctor.map₂_eqToHom, Cat.eqToHom_app] at h
    change (G.mapComp (v.op.toLoc ≫ u.op.toLoc) p).inv.toNatTrans.app y =
      (i.hom ≫ 𝟙 _) ≫ (G.mapComp u.op.toLoc p).inv.toNatTrans.app _ ≫
      (G.mapComp v.op.toLoc (u.op.toLoc ≫ p)).inv.toNatTrans.app y ≫ (backward G ((x.as ≫ u) ≫ v)).map (𝟙 _) ≫ eqToHom _
    erw [Category.comp_id, Functor.map_id, Category.id_comp]
    apply (cancel_epi i.inv).mp
    erw [Iso.inv_hom_id_assoc]
    exact h

def evaluation : Tensor (represented a) G ⥤ G.obj ⟨op a⟩ := (evaluationCocone a G).extend
def sectionFunctor : G.obj ⟨op a⟩ ⥤ Tensor (represented a) G :=
  (CategoryTheory.Prod.sectR (Discrete.mk (𝟙 a)) _) ⋙ insertion (represented a) G a

theorem eval_native {i : B} {p q : Discrete (a ⟶ i)} {x y : G.obj ⟨op i⟩} (h : p ⟶ q) (f : x ⟶ y) :
    (evaluation a G).map ((insertion (represented a) G i).map (productMap h f)) =
      (backward G p.as).map f ≫ eqToHom (by rw [Discrete.eq_of_hom h]; rfl) :=
  (evaluationCocone a G).extend_generator (Edge.native (F := represented a) (G := G) (i := i) h f)

theorem eval_balance {i j : B} (u : i ⟶ j) (p : Discrete (a ⟶ i)) (y : G.obj ⟨op j⟩) :
    (evaluation a G).map (balancing (represented a) G u p y).hom = (evalBalance a G u p y).hom :=
  (evaluationCocone a G).extend_generator (Edge.balance (F := represented a) (G := G) u p y)

def sectionEvaluation : sectionFunctor a G ⋙ evaluation a G ≅ 𝟭 _ :=
  NatIso.ofComponents (fun y => (Cat.Hom.toNatIso (G.mapId ⟨op a⟩)).app y) (by
    intro x y f
    change (evaluation a G).map ((insertion (represented a) G a).map (productMap (𝟙 (Discrete.mk (𝟙 a))) f)) ≫ _ = _
    rw [eval_native]
    erw [eqToHom_refl, Category.comp_id]
    exact (G.mapId ⟨op a⟩).hom.toNatTrans.naturality f)

end ContextualComposition.RelativeTensor.LeftUnit
