module
public import ContextualComposition.RepresentablePureUnits
public import ContextualComposition.RepresentableKleisliCoherent
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePureOriginalPorts
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli RepresentableKleisliOriginal RepresentableKleisliBicategory RepresentableKleisliConstraints
open RepresentablePureAssociativity RepresentablePureUnits
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
section Assembly
open RepresentableBicategoryAssembly
universe x y z
variable {Q : Type x} {H : Q → Q → Type y} [∀ a b, Category.{z} (H a b)]
theorem leftFromBuild (O : Operations H) (L : Laws O) {a b c : Q} (g : H a b) (h : H b c) :
    rW O (O.left g).hom h = (O.assoc (O.unit a) g h).hom ≫ (O.left (RepresentableBicategoryAssembly.cmp O g h)).hom :=
  @Bicategory.leftUnitor_whiskerRight Q (build O L) a b c g h
end Assembly
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
noncomputable def eta (X : Obj.{u,u} B) : X ⟶ obj S 1 X :=
  AmbientHorizontalFrames.E.{u,u} S X T.unit
noncomputable def ell {X Y : Obj.{u,u} B} (f : X ⟶ obj S 1 Y) :=
  RepresentableFoldLeftUnit.bare (p := eta T (obj S 1 Y)) (q := μ T Y) (squareE S T.unit f) (leftIso T Y)
variable {A B₀ C E₀ : B}
noncomputable def J₀ (f : yObj A ⟶ yObj B₀) : KH S A B₀ := f ≫ unit T B₀
noncomputable def C₀ (f : yObj A ⟶ yObj B₀) (g : yObj B₀ ⟶ yObj C) :
    compose T (J₀ T f) (J₀ T g) ≅ J₀ T (f ≫ g) :=
  c (action.{u,u} S 1) (μ T) (eta T) (ell T) f g
noncomputable def I₀ (A : B) : J₀ T (𝟙 (yObj A)) ≅ unit T A :=
  λ_ (unit T A)
theorem leftHom (g : KH S B₀ C) (h : KH S C E₀) :
    (reassociate T (unit T B₀) g h).hom ≫ (leftUnit T (compose T g h)).hom =
      composeCell T (leftUnit T g).hom (𝟙 h) := by
  have H := leftFromBuild (ops T) (laws T (RepresentableKleisliCoherent.actualLast T) (RepresentableKleisliCoherent.actualPent T))
    (a := ⟨B₀⟩) (b := ⟨C⟩) (c := ⟨E₀⟩) g h
  simpa only [RepresentableBicategoryAssembly.rW,RepresentableBicategoryAssembly.compCell,
    RepresentableBicategoryAssembly.cmp,ops,composeFunctor] using H.symm
theorem leftGeneral (g : KH S B₀ C) (h : KH S C E₀) :
    reassociate T (unit T B₀) g h ≪≫ leftUnit T (compose T g h) =
      wr (action S 1) (μ T) (leftUnit T g) h := by
  apply Iso.ext
  simp only [Iso.trans_hom,wr,whiskerRightIso_hom]
  rw [leftHom T g h]
  exact RepresentableAssociatorPrefix.first T (A := B₀) (D := C) (E := E₀) (leftUnit T g).hom h
theorem leftCoherence (g : KH S B₀ C) (h : KH S C E₀) :
    RepresentableKleisliGeneric.bend (action.{u,u} S 1) (μ T) (D T) (a T) (eta T (yObj B₀)) g h ≪≫
      ell T (RepresentableKleisliGeneric.cmp (action S 1) (μ T) g h) =
    wr (action S 1) (μ T) (ell T g) h := by
  have H := congrArg (fun j => j ≪≫ leftUnit T (compose T g h)) (bendPin T (unit T B₀) g h)
  exact H.trans (leftGeneral T g h)
theorem etaUnits (A : B) : ell T (eta T (yObj A)) = rightUnit T (unit T A) :=
  Iso.ext (@Bicategory.unitors_equal (Part B) (RepresentableKleisliCoherent.bicategory T) ⟨A⟩)
end ContextualComposition.GrothendieckStep.RepresentablePureOriginalPorts
