module
public import ContextualComposition.RelativeTensorUnitRowTransport
public import ContextualComposition.RelativeTensorIndexedLeftUnit
public import ContextualComposition.RelativeTensorWhiskeredEquivalence

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vY uY
variable {B : Type u} [Category.{v} B]

noncomputable def unitRowEquivalence (a : B) : Bicategory.Equivalence (row (unitModule B) a) (LeftUnit.represented a) := by
  letI (j : LocallyDiscrete B) : ((unitRowMap a).app j).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 ((LeftUnit.represented a).obj j)).IsEquivalence
  exact PseudonaturalInverse.equivalence (unitRowMap a)

section Bridge
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

def unitRowEndpoint : rightInner (unitModule B) Y ⟶ (LeftUnit.endpointFunctor Y).toPseudofunctor' :=
  strongToOrdinary (rightInner (unitModule B) Y) (LeftUnit.endpointFunctor Y)
    (fun a => mapFirst (G := Y) (unitRowMap a.as.unop))
    (fun f => unitRowMap_tensor_change Y f.as.unop (LeftUnit.precompose f.as.unop) (fun _ _ => rfl))
    (unitRow_source_id Y) (unitRow_source_comp Y)

theorem unitRowEndpoint_port {a b : B} (u : a ⟶ b) (z : (rightInner (unitModule B) Y).obj ⟨op b⟩) :
    (Second.port (unitRowEndpoint Y) u z).hom = 𝟙 _ := by
  change (eqToHom (unitRowMap_tensor_change Y u (LeftUnit.precompose u) (fun _ _ => rfl))).app z = _
  rw [eqToHom_app]; rfl

end Bridge

section Indexed
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vY uY,max u v uY})

/-- The left unitor on the actual iterated curried identity module. -/
def leftUnitor : rightInner (unitModule B) Y ⟶ Y :=
  unitRowEndpoint Y ≫ LeftUnit.indexedEvaluation.{v,u,vY,uY} Y

noncomputable def leftUnitEquivalence : Bicategory.Equivalence (rightInner (unitModule B) Y) Y := by
  letI (a : LocallyDiscrete Bᵒᵖ) : ((leftUnitor.{v,u,vY,uY} Y).app a).toFunctor.IsEquivalence :=
    ((whiskerFirst (unitRowEquivalence a.as.unop) Y).trans (LeftUnit.equivalence a.as.unop Y)).isEquivalence_functor
  exact PseudonaturalInverse.equivalence (leftUnitor.{v,u,vY,uY} Y)

theorem leftUnitor_part (a : B) : Second.part (leftUnitor.{v,u,vY,uY} Y) a =
    mapFirst (G := Y) (unitRowMap a) ⋙ LeftUnit.evaluation a Y := rfl

theorem leftUnitor_port {a b j : B} (u : a ⟶ b) (p : b ⟶ j) (y : Y.obj ⟨op j⟩) :
    (Second.port (leftUnitor.{v,u,vY,uY} Y) u ((insertM (unitModule B) Y b j).obj (Discrete.mk p,y))).hom =
      (Y.mapComp p.op.toLoc u.op.toLoc).hom.toNatTrans.app y := by
  unfold leftUnitor
  rw [Second.port_composite,unitRowEndpoint_port,Functor.map_id,Category.id_comp]
  rfl

theorem leftUnitor_native {a j : B} (p : a ⟶ j) {y y' : Y.obj ⟨op j⟩} (g : y ⟶ y') :
    (Second.part (leftUnitor.{v,u,vY,uY} Y) a).map
      ((insertM (unitModule B) Y a j).map (productMap (𝟙 (Discrete.mk p)) g)) = (backward Y p).map g := by
  have changeRow := First.on_native (G := Y) (i := j) (unitRowMap a) (𝟙 (Discrete.mk p)) g
  have evaluate := LeftUnit.eval_native a Y (𝟙 (Discrete.mk p)) g
  exact (congrArg (LeftUnit.evaluation a Y).map changeRow).trans (evaluate.trans (Category.comp_id _))

theorem leftUnitor_balance {a i j : B} (p : a ⟶ i) (v : i ⟶ j) (y : Y.obj ⟨op j⟩) :
    (Second.part (leftUnitor.{v,u,vY,uY} Y) a).map (balancing (row (unitModule B) a) Y v (Discrete.mk p) y).hom =
      (Y.mapComp v.op.toLoc p.op.toLoc).inv.toNatTrans.app y := by
  have changeRow := First.on_balance (G := Y) (unitRowMap a) v (Discrete.mk p) y
  have simplifyRow : (mapFirst (G := Y) (unitRowMap a)).map (balancing (row (unitModule B) a) Y v (Discrete.mk p) y).hom =
      (balancing (LeftUnit.represented a) Y v (Discrete.mk p) y).hom := by
    refine changeRow.trans ?_
    change _ ≫ (insertion (LeftUnit.represented a) Y j).map (𝟙 _) = _
    rw [Functor.map_id, Category.comp_id]
    rfl
  exact (congrArg (LeftUnit.evaluation a Y).map simplifyRow).trans (LeftUnit.eval_balance a Y v (Discrete.mk p) y)

end Indexed
end ContextualComposition.RelativeTensor.Iterated
