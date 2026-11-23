module
public import ContextualComposition.RelativeTensorMixedBundlingColumns

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section BundleOuterActualOrdinary
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
local notation "H" => middleComposite M N
local notation "HH" => middleComposite H H





theorem mixedOuterUnits :
    OrdinaryRawUnit (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n)
      (fun f => mixedColumnOutput.{v,u,vM,uM,vN,uN} M N s m n f) := by
  intro d a
  exact mixedMultiplicationOutput_identity.{v,u,vM,uM,vN,uN} M N s m n a.as.unop d

theorem mixedOuterComps :
    OrdinaryRawComp (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n)
      (fun f => mixedColumnOutput.{v,u,vM,uM,vN,uN} M N s m n f) := by
  intro a b c f g x
  exact mixedMultiplicationOutput_composition.{v,u,vM,uM,vN,uN} M N s m n x.as.unop f g

/-- The original mixed multiplication bundled as a strong map;
this endpoint-action result does not assert mixed algebra laws. -/
noncomputable def mixedMultiplication : HH ⟶ H :=
  strongCurriedFromOrdinaryRawLaws (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n)
    (fun f => mixedColumnOutput.{v,u,vM,uM,vN,uN} M N s m n f)
    (fun {a b} f => @actualColumnCube.{v,u,vM,uM,vN,uN} B _ M N s m n a b f)
    (mixedOuterUnits.{v,u,vM,uM,vN,uN} M N s m n)
    (mixedOuterComps.{v,u,vM,uM,vN,uN} M N s m n)

theorem mixedMultiplication_column (d : B) :
    (mixedMultiplication.{v,u,vM,uM,vN,uN} M N s m n).app ⟨d⟩ =
      mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n d := rfl

theorem mixedMultiplication_componentNamed (a d : B) :
    (((mixedMultiplication.{v,u,vM,uM,vN,uN} M N s m n).app ⟨d⟩).app ⟨op a⟩) =
      (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d ⟨op a⟩).toCatHom :=
  bundledColumnApp.{v,u,vM,uM,vN,uN} M N s m n d ⟨op a⟩
end BundleOuterActualOrdinary

section BundleOuterComponent
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
local notation "H" => middleComposite M N
local notation "HH" => middleComposite H H






theorem mixedMultiplication_app (a d : B) :
    (((mixedMultiplication.{v,u,vM,uM,vN,uN} M N s m n).app ⟨d⟩).app ⟨op a⟩).toFunctor =
      mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a d := by
  dsimp only [mixedMultiplication, strongCurriedFromOrdinaryRawLaws, strongCurriedFromRawLaws, strongCurriedFromEndpointLaws,
    mixedMultiplicationColumn, strongCatFromEndpointLaws, mixedColumnAt]
  rfl
end BundleOuterComponent

end ContextualComposition.RelativeTensor.Iterated
