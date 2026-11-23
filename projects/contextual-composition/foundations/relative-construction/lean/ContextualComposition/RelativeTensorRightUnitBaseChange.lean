module
public import ContextualComposition.RelativeTensorUnitModule
public import ContextualComposition.RelativeTensorRightContraction
public import ContextualComposition.RelativeTensorFactorCells
public import ContextualComposition.RelativeTensorGeneratorComparison

@[expose] public section
namespace ContextualComposition.RelativeTensor.RightUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vF uF
variable {B : Type u} [Category.{v} B] (F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF})
variable {a b : B} (k : a ⟶ b) (s : represented a ⟶ represented b)
variable (labels : ∀ (i : B) (p : Discrete (i ⟶ a)), ((Second.part s i).obj p).as = p.as ≫ k)
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The vertex comparison uses the chosen weak compositor after the specified identification of the postcomposed arrow. -/
def baseComponent {i : B} (x : F.obj ⟨i⟩) (p : Discrete (i ⟶ a)) :
    (forward F ((Second.part s i).obj p).as).obj x ≅ (forward F k).obj ((forward F p.as).obj x) :=
  eqToIso (congrArg (fun t => (forward F t).obj x) (labels i p)) ≪≫ (Cat.Hom.toNatIso (F.mapComp p.as.toLoc k.toLoc)).app x

private theorem nativeSquare {i : B} {x x' : F.obj ⟨i⟩} (f : x ⟶ x') (p : Discrete (i ⟶ a)) (r : i ⟶ b) (h : r = p.as ≫ k) :
    (forward F r).map f ≫ eqToHom (congrArg (fun t => (forward F t).obj x') h) ≫ (F.mapComp p.as.toLoc k.toLoc).hom.toNatTrans.app x' =
      (eqToHom (congrArg (fun t => (forward F t).obj x) h) ≫ (F.mapComp p.as.toLoc k.toLoc).hom.toNatTrans.app x) ≫ (forward F k).map ((forward F p.as).map f) := by
  subst r
  simp only [eqToHom_refl,Category.id_comp]
  exact (F.mapComp p.as.toLoc k.toLoc).hom.toNatTrans.naturality f

theorem base_native {i : B} {x x' : F.obj ⟨i⟩} {p q : Discrete (i ⟶ a)} (f : x ⟶ x') (g : p ⟶ q) :
    (mapSecond (F := F) s ⋙ evaluation b F).map ((insertion F (represented a) i).map (productMap f g)) ≫ (baseComponent F k s labels x' q).hom =
      (baseComponent F k s labels x p).hom ≫ (evaluation a F ⋙ forward F k).map ((insertion F (represented a) i).map (productMap f g)) := by
  obtain rfl : p = q := Discrete.ext (Discrete.eq_of_hom g)
  dsimp only [Functor.comp_map]
  rw [Second.on_native,eval_native,eval_native]
  simp only [eqToHom_refl,Category.comp_id]
  exact nativeSquare F k f p _ (labels i p)

private theorem assocSquare {i j : B} (u : i ⟶ j) (p : j ⟶ a) (x : F.obj ⟨i⟩) :
    eqToHom (congrArg (fun r => (forward F r).obj x) (Category.assoc u p k)) ≫
      (F.mapComp u.toLoc (p ≫ k).toLoc).hom.toNatTrans.app x ≫ (F.mapComp p.toLoc k.toLoc).hom.toNatTrans.app ((forward F u).obj x) =
    (F.mapComp (u ≫ p).toLoc k.toLoc).hom.toNatTrans.app x ≫ (forward F k).map ((F.mapComp u.toLoc p.toLoc).hom.toNatTrans.app x) := by
  have h := F.mapComp_assoc_left_hom_app u.toLoc p.toLoc k.toLoc x
  simp only [Bicategory.Strict.associator_eqToIso,eqToIso.hom,PrelaxFunctor.map₂_eqToHom,Cat.eqToHom_app] at h
  exact h.symm

private theorem transportedAssoc {i j : B} (u : i ⟶ j) (p : j ⟶ a) (x : F.obj ⟨i⟩)
    (r : i ⟶ b) (t : j ⟶ b) (hr : r = (u ≫ p) ≫ k) (ht : t = p ≫ k) :
    eqToHom (congrArg (fun l => (forward F l).obj x) (hr.trans ((Category.assoc u p k).trans (congrArg (u ≫ ·) ht.symm)))) ≫
      (F.mapComp u.toLoc t.toLoc).hom.toNatTrans.app x ≫
        eqToHom (congrArg (fun l => (forward F l).obj ((forward F u).obj x)) ht) ≫
          (F.mapComp p.toLoc k.toLoc).hom.toNatTrans.app ((forward F u).obj x) =
    eqToHom (congrArg (fun l => (forward F l).obj x) hr) ≫
      (F.mapComp (u ≫ p).toLoc k.toLoc).hom.toNatTrans.app x ≫ (forward F k).map ((F.mapComp u.toLoc p.toLoc).hom.toNatTrans.app x) := by
  subst r; subst t
  simp only [eqToHom_refl,Category.id_comp]
  exact assocSquare F k u p x

theorem base_balance {i j : B} (u : i ⟶ j) (x : F.obj ⟨i⟩) (p : Discrete (j ⟶ a)) :
    (mapSecond (F := F) s ⋙ evaluation b F).map (balancing F (represented a) u x p).hom ≫
      (baseComponent F k s labels ((forward F u).obj x) p).hom =
    (baseComponent F k s labels x ((backward (represented a) u).obj p)).hom ≫ (evaluation a F ⋙ forward F k).map (balancing F (represented a) u x p).hom := by
  dsimp only [Functor.comp_map]
  rw [Second.on_balance,Functor.map_comp,eval_native,eval_balance,eval_balance]
  simp only [Functor.map_id,Category.id_comp,baseComponent,Iso.trans_hom,eqToIso.hom,Category.assoc]
  exact transportedAssoc F k u p.as x _ _ (labels i ((backward (represented a) u).obj p)) (labels j p)

/-- Base change of right-unit evaluation along a strong map acting by postcomposition on represented labels. -/
def baseChange :
    mapSecond (F := F) s ⋙ evaluation b F ≅ evaluation a F ⋙ forward F k :=
  isoOfGenerators (fun z => baseComponent F k s labels z.as.first z.as.second)
    (fun f g => base_native F k s labels f g) (fun u x p => base_balance F k s labels u x p)

@[simp] theorem baseChange_app (z : Tensor F (represented a)) :
    (baseChange F k s labels).hom.app z = (baseComponent F k s labels z.as.first z.as.second).hom := rfl

/-- Base change along the actual postcomposition of the identity module. -/
def indexedBase {a b : B} (k : a ⟶ b) :
    ((Iterated.leftInner F (Iterated.unitModule B)).map k.toLoc).toFunctor ⋙ evaluation b F ≅ evaluation a F ⋙ forward F k :=
  baseChange F k (Iterated.unitPostcompose k) (fun _ _ => rfl)

/-- The component on every vertex is the original weak compositor, including for non-strict actions. -/
@[simp] theorem indexedBase_app {a b : B} (k : a ⟶ b) (z : Tensor F (represented a)) :
    (indexedBase F k).hom.app z = (F.mapComp z.as.second.as.toLoc k.toLoc).hom.toNatTrans.app z.as.first := by
  change 𝟙 _ ≫ _ = _
  apply Category.id_comp

end ContextualComposition.RelativeTensor.RightUnit
