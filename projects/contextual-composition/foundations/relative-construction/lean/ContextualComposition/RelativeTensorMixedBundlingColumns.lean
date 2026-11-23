module
public import ContextualComposition.RelativeTensorMixedBundlingInterfaces

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section BundleJointObligationStatement
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
local notation "H" => middleComposite M N
local notation "HH" => middleComposite H H

set_option maxHeartbeats 200000 in
noncomputable def mixedColumnAt (d : B) (a : LocallyDiscrete Bᵒᵖ) :
    (column HH d).obj a ⥤ (column H d).obj a :=
  mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a.as.unop d

set_option maxHeartbeats 200000 in
noncomputable def mixedColumnInput (d : B) {a b : LocallyDiscrete Bᵒᵖ} (f : a ⟶ b) :
    ((column HH d).map f).toFunctor ⋙ mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d b ≅
    mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d a ⋙ ((column H d).map f).toFunctor :=
  mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n f.as.unop d

set_option maxHeartbeats 200000 in
noncomputable def mixedMultiplicationColumn (d : B) : column HH d ⟶ column H d :=
  strongCatFromEndpointLaws (F := column HH d) (G := column H d)
    (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d)
    (fun f => mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n d f)
    (fun a => mixedMultiplicationInput_identity.{v,u,vM,uM,vN,uN} M N s m n a.as.unop d)
    (fun f g => mixedMultiplicationInput_composition.{v,u,vM,uM,vN,uN} M N s m n g.as.unop f.as.unop d)

theorem bundledColumnApp (d : B) (a : LocallyDiscrete Bᵒᵖ) :
    (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n d).app a =
      (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d a).toCatHom :=
  rfl

theorem bundledColumnInput (d : B) {a b : LocallyDiscrete Bᵒᵖ} (f : a ⟶ b) :
    (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n d).naturality f =
      Cat.Hom.isoMk (mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n d f) :=
  rfl

set_option maxHeartbeats 150000 in
noncomputable def mixedColumnOutput {c d : B} (g : c ⟶ d) (a : LocallyDiscrete Bᵒᵖ) :
    (((HH).map g.toLoc).app a).toFunctor ⋙ ((mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n d).app a).toFunctor ≅
    ((mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n c).app a).toFunctor ⋙ (((H).map g.toLoc).app a).toFunctor :=
  mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a.as.unop g

set_option maxHeartbeats 250000 in
def mixedColumnJointObligation {c d : B} (g : c ⟶ d) : Prop :=
    ColumnCubeLaw ((HH).map g.toLoc) ((H).map g.toLoc)
      (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n c)
      (mixedMultiplicationColumn.{v,u,vM,uM,vN,uN} M N s m n d)
      (mixedColumnOutput.{v,u,vM,uM,vN,uN} M N s m n g)
end BundleJointObligationStatement

section BundleBoundaryActual
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
local notation "H" => middleComposite M N
local notation "HH" => middleComposite H H



noncomputable def rawOutput {c d : B} (g : c ⟶ d) (a : LocallyDiscrete Bᵒᵖ) :
    (((HH).map g.toLoc).app a).toFunctor ⋙ (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d) a ≅ (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n c) a ⋙ (((H).map g.toLoc).app a).toFunctor :=
  mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a.as.unop g


set_option maxHeartbeats 150000 in
theorem actualRawCube {c d : B} (g : c ⟶ d) :
    RawColumnCube ((HH).map g.toLoc) ((H).map g.toLoc) (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n c) (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d) (fun f => (mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n c) f) (fun f => (mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n d) f) (rawOutput.{v,u,vM,uM,vN,uN} M N s m n g) := by
  intro a b f
  exact mixedMultiplicationInputOutput_compatibility.{v,u,vM,uM,vN,uN} M N s m n f.as.unop g

set_option maxHeartbeats 180000 in
theorem actualColumnCube {c d : B} (g : c ⟶ d) :
    mixedColumnJointObligation.{v,u,vM,uM,vN,uN} M N s m n g := by
  exact ColumnCubeLaw.of_constructedColumns ((HH).map g.toLoc) ((H).map g.toLoc)
    (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n c) (mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d) (fun f => (mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n c) f) (fun f => (mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n d) f) (rawOutput.{v,u,vM,uM,vN,uN} M N s m n g)
    (fun a => mixedMultiplicationInput_identity.{v,u,vM,uM,vN,uN} M N s m n a.as.unop c)
    (fun f g => mixedMultiplicationInput_composition.{v,u,vM,uM,vN,uN} M N s m n g.as.unop f.as.unop c)
    (fun a => mixedMultiplicationInput_identity.{v,u,vM,uM,vN,uN} M N s m n a.as.unop d)
    (fun f g => mixedMultiplicationInput_composition.{v,u,vM,uM,vN,uN} M N s m n g.as.unop f.as.unop d)
    (actualRawCube.{v,u,vM,uM,vN,uN} M N s m n g)
end BundleBoundaryActual

section BundleColumnRawPins
universe v u vM uM vN uN
variable {B : Type u} [Category.{v} B]
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
local notation "H" => middleComposite M N
local notation "HH" => middleComposite H H



theorem namedColumnAt_eq (a d : B) :
    mixedColumnAt.{v,u,vM,uM,vN,uN} M N s m n d ⟨op a⟩ =
    mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a d := rfl

theorem namedColumnInput_eq {a b : B} (f : a ⟶ b) (d : B) :
    mixedColumnInput.{v,u,vM,uM,vN,uN} M N s m n d f.op.toLoc =
    mixedMultiplicationInput.{v,u,vM,uM,vN,uN} M N s m n f d := rfl


theorem rawOutput_eq (a : B) {c d : B} (g : c ⟶ d) :
    rawOutput.{v,u,vM,uM,vN,uN} M N s m n g ⟨op a⟩ =
      mixedMultiplicationOutput.{v,u,vM,uM,vN,uN} M N s m n a g := rfl

theorem mixedColumnOutput_raw (a : B) {c d : B} (g : c ⟶ d) :
    HEq (mixedColumnOutput.{v,u,vM,uM,vN,uN} M N s m n g ⟨op a⟩)
      (rawOutput.{v,u,vM,uM,vN,uN} M N s m n g ⟨op a⟩) := HEq.rfl
end BundleColumnRawPins

end ContextualComposition.RelativeTensor.Iterated
