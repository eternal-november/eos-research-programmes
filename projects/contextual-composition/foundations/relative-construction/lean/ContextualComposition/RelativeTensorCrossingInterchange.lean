module
public import ContextualComposition.RelativeTensorCrossingPayload
public import ContextualComposition.RelativeTensorAssociatorFirstChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
universe v u vD uD vX uX vM uM
variable {B : Type u} [Category.{v} B] {D : Type uD} [Category.{vD} D]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (t : X ⟶ X')
variable {P Q : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})} (s : P ⟶ Q)
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

private theorem first_hom (P : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})) {a b : LocallyDiscrete D} (f : a ⟶ b) (z : Tensor X (P.obj a)) :
    ((firstMap t P).naturality f).hom.toNatTrans.app z = 𝟙 _ := by
  change (eqToHom (factor_order t (P.map f)).symm).app z = _
  rw [eqToHom_app]; rfl

/-- The order comparison on payloads is the binary tensor interchange on each full column. -/
def crossingInterchangeIso : firstMap t P ≫ crossingPayload X' s ≅ crossingPayload X s ≫ firstMap t Q :=
  Pseudofunctor.StrongTrans.isoMk (fun a => Parametric.interchange t (s.app a)) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (Parametric.interchange t (s.app b)).hom.toNatTrans.app _ ≫
      𝟙 _ ≫ (mapFirst (G := Q.obj b) t).map ((crossingSquare X s f).hom.toNatTrans.app z) ≫ 𝟙 _ ≫
        ((firstMap t Q).naturality f).hom.toNatTrans.app _ ≫ 𝟙 _ =
      (𝟙 _ ≫ (mapSecond (F := X') (s.app b)).map (((firstMap t P).naturality f).hom.toNatTrans.app z) ≫ 𝟙 _ ≫
        (crossingSquare X' s f).hom.toNatTrans.app _ ≫ 𝟙 _) ≫
        ((leftInner X' Q).map f).toFunctor.map ((Parametric.interchange t (s.app a)).hom.toNatTrans.app z)
    simp only [Parametric.interchange_app,first_hom,Functor.map_id,Category.id_comp,Category.comp_id,crossingSquare_app]
    erw [First.on_native (G := Q.obj b) t,Functor.map_id]
    rfl)

@[simp] theorem crossingInterchangeIso_app (a : LocallyDiscrete D) (z : Tensor X (P.obj a)) :
    ((crossingInterchangeIso t s).hom.as.app a).toNatTrans.app z = 𝟙 _ :=
  Parametric.interchange_app t (s.app a) z

private theorem equalOfTransport {A U : Type*} [Bicategory A] [Bicategory U] {F G : A ⥤ᵖ U}
    (p q : F ⟶ G) (m : p ⟶ q) (e : p.app = q.app) (h : ∀ x, m.as.app x = eqToHom (congrFun e x)) : p = q := by
  cases p with
  | mk pa pn pnn pi pc =>
    cases q with
    | mk qa qn qnn qi qc =>
      cases e
      have n : @pn = @qn := by
        funext a b f
        apply Iso.ext
        have sq := m.as.naturality f
        rw [h a,h b] at sq
        simpa using sq.symm
      cases n
      rfl

/-- First-factor payload change strictly commutes with a supplied strong map of curried modules, including their naturality squares. -/
theorem crossingInterchange : firstMap t P ≫ crossingPayload X' s = crossingPayload X s ≫ firstMap t Q := by
  let e (a : LocallyDiscrete D) := congrArg Functor.toCatHom (factor_order t (s.app a))
  apply equalOfTransport _ _ (crossingInterchangeIso t s).hom (funext e)
  intro a
  apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
  rw [crossingInterchangeIso_app,Cat.Hom₂.eqToHom_toNatTrans,eqToHom_app]
  rfl

end ContextualComposition.RelativeTensor.Iterated
