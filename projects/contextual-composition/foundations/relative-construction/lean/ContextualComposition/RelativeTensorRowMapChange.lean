module
public import ContextualComposition.RelativeTensorModuleRows

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
universe v u vC uC vM uM
variable {B : Type u} [Category.{v} B] {C : Type uC} [Category.{vC} C]
variable {M N : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM})}
variable (s : M ⟶ N) {a b : B} (u : a ⟶ b)

private theorem rearrange {D : Type*} [Category* D] {a b c d e f : D} (L : a ≅ b) (R : e ≅ f)
    (p : a ⟶ c) (q : c ⟶ e) (h : b ⟶ d) (k : d ⟶ f) (w : p ≫ q ≫ R.hom = L.hom ≫ h ≫ k) :
    h ≫ k ≫ R.inv = L.inv ≫ p ≫ q := by
  have eq := congrArg (fun g => L.inv ≫ g ≫ R.inv) w
  simpa [Category.assoc] using eq.symm

/-- The full strong comparison across a contravariant endpoint change uses the supplied naturality isomorphism at each covariant index. -/
def rowMap_changeIso :
    Middle.change M u.op.toLoc ≫ rowMap s a ≅ rowMap s b ≫ Middle.change N u.op.toLoc :=
  Pseudofunctor.StrongTrans.isoMk (fun j => (s.app j).naturality u.op.toLoc) (by
    intro i j f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext x
    let U := u.op.toLoc
    let Sa := ((s.app j).app ⟨op a⟩).toFunctor
    let Sb := ((s.app i).app ⟨op b⟩).toFunctor
    let Ma := ((M.obj i).map U).toFunctor
    let Nb := ((N.obj j).map U).toFunctor
    let Mf := ((M.map f).app ⟨op b⟩).toFunctor
    let Nf := ((N.map f).app ⟨op a⟩).toFunctor
    let l := Sa.mapIso ((Cat.Hom.toNatIso ((M.map f).naturality U)).app x)
    let r := (Cat.Hom.toNatIso ((N.map f).naturality U)).app (Sb.obj x)
    let p := ((s.naturality f).hom.as.app ⟨op a⟩).toNatTrans.app (Ma.obj x)
    let q := Nf.map (((s.app i).naturality U).hom.toNatTrans.app x)
    let h := ((s.app j).naturality U).hom.toNatTrans.app (Mf.obj x)
    let k := Nb.map (((s.naturality f).hom.as.app ⟨op b⟩).toNatTrans.app x)
    have original := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans ((s.naturality f).hom.as.naturality U)) x
    change p ≫ 𝟙 _ ≫ q ≫ 𝟙 _ ≫ r.hom ≫ 𝟙 _ = (𝟙 _ ≫ l.hom ≫ 𝟙 _ ≫ h ≫ 𝟙 _) ≫ k at original
    simp only [Category.comp_id,Category.id_comp,Category.assoc] at original
    change h ≫ 𝟙 _ ≫ k ≫ 𝟙 _ ≫ r.inv ≫ 𝟙 _ = (𝟙 _ ≫ l.inv ≫ 𝟙 _ ≫ p ≫ 𝟙 _) ≫ q
    simp only [Category.id_comp,Category.comp_id,Category.assoc]
    exact rearrange l r p q h k original)

@[simp] theorem rowMap_changeIso_component (j : LocallyDiscrete C) :
    (rowMap_changeIso s u).hom.as.app j = ((s.app j).naturality u.op.toLoc).hom := rfl

end ContextualComposition.RelativeTensor.Iterated
