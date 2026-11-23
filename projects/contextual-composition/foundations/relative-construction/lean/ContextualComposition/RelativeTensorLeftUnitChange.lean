module
public import ContextualComposition.RelativeTensorLeftContraction
public import ContextualComposition.RelativeTensorFactorCells
public import ContextualComposition.RelativeTensorGeneratorComparison

@[expose] public section
namespace ContextualComposition.RelativeTensor.LeftUnit
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vG uG
variable {B : Type u} [Category.{v} B] {a b : B} (f : a ⟶ b) (G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG})

/-- Precomposition between the two discrete covariant representables. -/
def precompose {a b : B} (f : a ⟶ b) : represented b ⟶ represented a where
  app i := (Discrete.functor (fun p : b ⟶ i.as => Discrete.mk (f ≫ p))).toCatHom
  naturality {i j} u := Cat.Hom.isoMk (NatIso.ofComponents (fun p => eqToIso (Discrete.ext (Category.assoc f p.as u.as).symm))
    (by intros; exact Discrete.hom_eq (α := a ⟶ j.as)))
  naturality_naturality {i j r t} m := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; exact Discrete.hom_eq (α := a ⟶ j.as)
  naturality_id i := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; exact Discrete.hom_eq (α := a ⟶ i.as)
  naturality_comp {i j k} u v := by apply Cat.Hom₂.ext; apply NatTrans.ext; funext p; exact Discrete.hom_eq (α := a ⟶ k.as)

private theorem discreteStrong_ext {r s : represented b ⟶ represented a}
    (h : ∀ (i : LocallyDiscrete B) (p : Discrete (b ⟶ i.as)), ((r.app i).toFunctor.obj p).as = ((s.app i).toFunctor.obj p).as) : r = s := by
  have ha : r.app = s.app := by
    funext i
    apply Cat.Hom.ext
    apply Functor.ext (fun p => Discrete.ext (h i p))
  cases r with
  | mk r α =>
    cases s with
    | mk s β =>
      change r = s at ha
      subst s
      have hn : @α = @β := by
        funext i j u
        apply Iso.ext; apply Cat.Hom₂.ext; apply NatTrans.ext; funext p
        exact Discrete.hom_eq (α := a ⟶ j.as)
      cases hn
      rfl

/-- An action on discrete representables is determined by its arrow labels, including all its strong comparison cells. -/
theorem precompose_unique (s : represented b ⟶ represented a)
    (h : ∀ (i : LocallyDiscrete B) (p : Discrete (b ⟶ i.as)), ((s.app i).toFunctor.obj p).as = f ≫ p.as) :
    s = precompose f := discreteStrong_ext h

theorem precompose_id (a : B) : precompose (𝟙 a) = 𝟙 (represented a) :=
  discreteStrong_ext (fun _ p => Category.id_comp p.as)

theorem precompose_comp {c : B} (g : b ⟶ c) : precompose (f ≫ g) = precompose g ≫ precompose f :=
  discreteStrong_ext (fun _ p => Category.assoc f g p.as)

def changeComponent (z : Tensor (represented b) G) :
    (mapFirst (precompose f) ⋙ evaluation a G).obj z ≅ (evaluation b G ⋙ backward G f).obj z :=
  (Cat.Hom.toNatIso (G.mapComp z.as.first.as.op.toLoc f.op.toLoc)).app z.as.second

theorem native_change {i : B} {p q : Discrete (b ⟶ i)} {y y' : G.obj ⟨op i⟩} (l : p ⟶ q) (t : y ⟶ y') :
    (mapFirst (precompose f) ⋙ evaluation a G).map ((insertion (represented b) G i).map (productMap l t)) ≫ (changeComponent f G _).hom =
      (changeComponent f G _).hom ≫ (evaluation b G ⋙ backward G f).map ((insertion (represented b) G i).map (productMap l t)) := by
  obtain rfl : p = q := Discrete.ext (Discrete.eq_of_hom l)
  obtain rfl : l = 𝟙 p := Subsingleton.elim _ _
  simp only [Functor.comp_map]
  rw [First.on_native,eval_native,eval_native]
  erw [eqToHom_refl,Category.comp_id,eqToHom_refl,Category.comp_id]
  exact (G.mapComp p.as.op.toLoc f.op.toLoc).hom.toNatTrans.naturality t

private theorem move {C : Type*} [Category* C] {x y z r t : C} (A : x ≅ y) (e : x ⟶ z) (B : z ≅ r) (k : y ⟶ t) (D : r ≅ t)
    (h : A.hom ≫ k = e ≫ B.hom ≫ D.hom) : (A.inv ≫ e) ≫ B.hom = k ≫ D.inv := by
  apply (cancel_epi A.hom).mp
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  rw [← Category.assoc A.hom k,h]
  simp

theorem balance_change {i j : B} (u : i ⟶ j) (p : Discrete (b ⟶ i)) (y : G.obj ⟨op j⟩) :
    (mapFirst (precompose f) ⋙ evaluation a G).map (balancing (represented b) G u p y).hom ≫ (changeComponent f G _).hom =
      (changeComponent f G _).hom ≫ (evaluation b G ⋙ backward G f).map (balancing (represented b) G u p y).hom := by
  simp only [Functor.comp_map]
  rw [First.on_balance,Functor.map_comp,eval_balance,eval_native,eval_balance]
  erw [Functor.map_id,Category.id_comp]
  let U := u.op.toLoc
  let P := p.as.op.toLoc
  let F := f.op.toLoc
  have h := G.mapComp_assoc_right_hom_app U P F y
  simp only [Bicategory.Strict.associator_eqToIso,eqToIso.inv,PrelaxFunctor.map₂_eqToHom,Cat.eqToHom_app] at h
  exact move ((Cat.Hom.toNatIso (G.mapComp U (P ≫ F))).app y) _
    ((Cat.Hom.toNatIso (G.mapComp (U ≫ P) F)).app y) _ ((backward G f).mapIso ((Cat.Hom.toNatIso (G.mapComp U P)).app y)) h

/-- The left evaluation square for an arbitrary change of the represented endpoint and an arbitrary weak contravariant Cat-action. -/
def baseChange : mapFirst (precompose f) ⋙ evaluation a G ≅ evaluation b G ⋙ backward G f :=
  isoOfGenerators (changeComponent f G) (native_change f G) (balance_change f G)

theorem baseChange_app (z : Tensor (represented b) G) :
    (baseChange f G).hom.app z = (G.mapComp z.as.first.as.op.toLoc f.op.toLoc).hom.toNatTrans.app z.as.second := rfl

end ContextualComposition.RelativeTensor.LeftUnit
