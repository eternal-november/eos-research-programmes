module
public import ContextualComposition.RelativeTensorUniversal
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section
namespace ContextualComposition.RelativeTensor.RightUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory
universe v u vF uF
variable {B : Type u} [Category.{v} B]
variable (a : B) (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF})
set_option backward.isDefEq.respectTransparency false
attribute [local simp] PrelaxFunctor.map₂_eqToHom

abbrev represented := (yoneda.obj a ⋙ typeToCat).toPseudofunctor'

def evalFiber (i : B) : (F.obj ⟨i⟩ × Discrete (i ⟶ a)) ⥤ F.obj ⟨a⟩ where
  obj s := (forward F s.2.as).obj s.1
  map {s t} f := (forward F s.2.as).map f.1 ≫ eqToHom (by rw [Discrete.eq_of_hom f.2])
  map_id s := by simp
  map_comp {x y z} f g := by
    obtain ⟨p,⟨x⟩⟩ := x
    obtain ⟨q,⟨y⟩⟩ := y
    obtain ⟨r,⟨z⟩⟩ := z
    obtain rfl : x = y := Discrete.eq_of_hom f.2
    obtain rfl : x = z := Discrete.eq_of_hom g.2
    simp

def evalBalance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (y : Discrete (j ⟶ a)) :
    (evalFiber a F i).obj (x,(backward (represented a) u).obj y) ≅
      (evalFiber a F j).obj ((forward F u).obj x,y) :=
  (Cat.Hom.toNatIso (F.mapComp u.toLoc y.as.toLoc)).app x

private theorem transportMap {i j : B} {p q : i ⟶ j} (h : p = q) {x y : F.obj ⟨i⟩} (f : x ⟶ y) :
    eqToHom (congrArg (fun t => (forward F t).obj x) h) ≫ (forward F q).map f =
      (forward F p).map f ≫ eqToHom (congrArg (fun t => (forward F t).obj y) h) := by
  subst q
  simp

def evaluationCocone : Cocone F (represented a) (F.obj ⟨a⟩) where
  fiber := evalFiber a F
  bal := evalBalance a F
  natural := by
    intro i j u x x' y y' p q
    obtain rfl : y = y' := Discrete.ext (Discrete.eq_of_hom q)
    change ((forward F (u ≫ y.as)).map p ≫ eqToHom _) ≫
      (F.mapComp u.toLoc y.as.toLoc).hom.toNatTrans.app x' =
      (F.mapComp u.toLoc y.as.toLoc).hom.toNatTrans.app x ≫ (forward F y.as).map ((forward F u).map p) ≫ eqToHom _
    erw [eqToHom_refl, Category.comp_id, eqToHom_refl, Category.comp_id]
    exact (F.mapComp u.toLoc y.as.toLoc).hom.toNatTrans.naturality p
  unit x y := by
    change (F.mapComp (𝟙 _) y.as.toLoc).hom.toNatTrans.app x =
      (forward F ((𝟙 _) ≫ y.as)).map ((F.mapId _).inv.toNatTrans.app x) ≫ eqToHom _
    simp [F.mapComp_id_left_hom_app, Bicategory.Strict.leftUnitor_eqToIso]
    exact transportMap F (Category.id_comp y.as) _
  comp u v x y := by
    let p := y.as.toLoc
    let i := (forward F y.as).mapIso ((Cat.Hom.toNatIso (F.mapComp u.toLoc v.toLoc)).app x)
    have h := F.mapComp_assoc_left_hom_app u.toLoc v.toLoc p x
    simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
      Cat.eqToHom_app] at h
    change (F.mapComp (u.toLoc ≫ v.toLoc) p).hom.toNatTrans.app x =
      ((forward F ((u ≫ v) ≫ y.as)).map (𝟙 x) ≫ eqToHom _) ≫
      (F.mapComp u.toLoc (v.toLoc ≫ p)).hom.toNatTrans.app x ≫
      (F.mapComp v.toLoc p).hom.toNatTrans.app _ ≫ i.inv ≫ 𝟙 _
    erw [Functor.map_id, Category.id_comp, Category.comp_id]
    apply (cancel_mono i.hom).mp
    simp only [Category.assoc]
    erw [i.inv_hom_id, Category.comp_id]
    exact h

def evaluation : Tensor F (represented a) ⥤ F.obj ⟨a⟩ := (evaluationCocone a F).extend
def sectionFunctor : F.obj ⟨a⟩ ⥤ Tensor F (represented a) :=
  (CategoryTheory.Prod.sectL _ (Discrete.mk (𝟙 a))) ⋙ insertion F (represented a) a

theorem eval_native {i : B} {p q : Discrete (i ⟶ a)} {x y : F.obj ⟨i⟩} (f : x ⟶ y) (h : p ⟶ q) :
    (evaluation a F).map ((insertion F (represented a) i).map (productMap f h)) =
      (forward F p.as).map f ≫ eqToHom (by rw [Discrete.eq_of_hom h]; rfl) :=
  (evaluationCocone a F).extend_generator (Edge.native (F := F) (G := represented a) (i := i) f h)

theorem eval_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (p : Discrete (j ⟶ a)) :
    (evaluation a F).map (balancing F (represented a) u x p).hom = (evalBalance a F u x p).hom :=
  (evaluationCocone a F).extend_generator (Edge.balance (F := F) (G := represented a) u x p)

def sectionEvaluation : sectionFunctor a F ⋙ evaluation a F ≅ 𝟭 _ :=
  NatIso.ofComponents (fun x => (Cat.Hom.toNatIso (F.mapId ⟨a⟩)).app x) (by
    intro x y f
    change (evaluation a F).map ((insertion F (represented a) a).map (productMap f (𝟙 (Discrete.mk (𝟙 a))))) ≫ _ = _
    rw [eval_native]
    erw [eqToHom_refl, Category.comp_id]
    exact (F.mapId ⟨a⟩).hom.toNatTrans.naturality f)

end ContextualComposition.RelativeTensor.RightUnit
