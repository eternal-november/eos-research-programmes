module
public import ContextualComposition.RepresentablePurePseudofunctor
public import ContextualComposition.RepresentablePureBaseChange
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentablePurePins
open CategoryTheory CategoryTheory.Bicategory
open AmbientBicategory AmbientCoherentPseudomonad RepresentableKleisli RepresentableKleisliOriginal
open AmbientHorizontalFrames AmbientHorizontalDiagrams
open RepresentableKleisliCoherent RepresentableKleisliBicategory RepresentableKleisliConstraints
open RepresentablePureOriginalPorts RepresentablePurePseudofunctor
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 550000
set_option linter.style.haveILetI false
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A C E A' C' : B}

theorem native (f : A ⟶ C) :
    letI : Bicategory (Part B) := bicategory T
    (commaEquiv (S := S) (A := A) (D := C)).functor.obj ((RepresentablePurePseudofunctor.pure T).map f.toLoc) =
      CostructuredArrow.mk (Y := T.unit.grade A) (T.unit.discharge A ≫ f) := by
  change (RepresentableComma.read (P.extend A) C).obj (row (pureK T f)) = _
  rw [pureKAt]
  rfl

/-- The inverse local Yoneda chart takes the native pure arrow to a specified
isomorphism with actual Kleisli insertion, not to a claimed strict inverse. -/
noncomputable def encodedPureIso (f : A ⟶ C) :
    (commaEquiv (S := S) (A := A) (D := C)).inverse.obj
      (CostructuredArrow.mk (Y := T.unit.grade A) (T.unit.discharge A ≫ f)) ≅ pureK T f :=
  let E₀ := commaEquiv (S := S) (A := A) (D := C)
  eqToIso (congrArg E₀.inverse.obj (native T f).symm) ≪≫ (E₀.unitIso.app (pureK T f)).symm

theorem unit (A : B) :
    letI : Bicategory (Part B) := bicategory T
    (RepresentablePurePseudofunctor.pure T).mapId (LocallyDiscrete.mk A) = eqToIso (RepresentablePureKleisli.identity T A) := by
  letI : Bicategory (Part B) := bicategory T
  have H := RepresentablePureBaseChange.unit (pureBaseFunctor (B := B)) (bridge T) A
  change (RepresentablePurePseudofunctor.pure T).mapId (LocallyDiscrete.mk A) =
    eqToIso (congrArg (· ≫ RepresentableKleisli.unit T A) (RepresentablePure.pure_id A)) ≪≫ I₀ T A at H
  refine H.trans ?_
  unfold I₀
  rw [Strict.leftUnitor_eqToIso, RepresentableStrictFold.castIsoComp]
  rfl

theorem prePin (f : A ⟶ C) (g : KH S C E) :
    RepresentablePureBend.pre (action.{u,u} S 1) (μ T) (eta T) (ell T) (pureMap f) g = preBend T f g := by
  exact Iso.trans_assoc
    (whiskerRightIso (α_ (pureMap f) (RepresentableKleisli.unit T C) (K S g)) (M S (yObj E) T.mult))
    (α_ (pureMap f) (RepresentableKleisli.unit T C ≫ K S g) (M S (yObj E) T.mult))
    (whiskerLeftIso (pureMap f) (leftUnit T g))

theorem cPin (f : A ⟶ C) (g : C ⟶ E) :
    C₀ T (pureMap f) (pureMap g) =
    preBend T f (pureK T g) ≪≫ (α_ (pureMap f) (pureMap g) (RepresentableKleisli.unit T E)).symm :=
  congrArg (fun t => t ≪≫ (α_ (pureMap f) (pureMap g) (RepresentableKleisli.unit T E)).symm) (prePin T f (pureK T g))

theorem bodyBinary (f : A ⟶ C) (g : C ⟶ E) :
    C₀ T (pureMap f) (pureMap g) ≪≫
      eqToIso (congrArg (· ≫ RepresentableKleisli.unit T E) (RepresentablePure.pure_comp f g).symm) =
      RepresentablePureKleisli.comp T f g := by
  rw [cPin]
  exact RepresentablePureBaseChange.foldSuffix (Q := Obj.{u,u} B)
    (x := yObj A) (y := yObj C) (z := yObj E) (w := KObj S E)
    (pureMap f) (pureMap g) (RepresentableKleisli.unit T E) (preBend T f (pureK T g))
    (congrArg (· ≫ RepresentableKleisli.unit T E) (RepresentablePure.pure_comp f g).symm)

set_option linter.defProp false in
/-- The assembled forward binary comparator with its actual core chart
and ordinary-base equality cast still exposed. -/
def binaryChart (f : A ⟶ C) (g : C ⟶ E) :=
  RepresentablePureBaseChange.buildComp (pureBaseFunctor (B := B))
    (laws T (actualLast T) (actualPent T)) (faces T) f g

/-- The pure maps in the previously checked native square realization are
exactly the maps of the assembled ordinary-base pseudofunctor. -/
noncomputable def bent (u : A ⟶ A') (v : C ⟶ C') (x : KH S A C) (y : KH S A' C') :
    letI : Bicategory (Part B) := bicategory T
    let x₀ : (⟨A⟩ : Part B) ⟶ ⟨C⟩ := x
    let y₀ : (⟨A'⟩ : Part B) ⟶ ⟨C'⟩ := y
    (x₀ ≫ (RepresentablePurePseudofunctor.pure T).map v.toLoc ⟶
      (RepresentablePurePseudofunctor.pure T).map u.toLoc ≫ y₀) ≃
      RepresentableNativeEndpoints.Square u v (row x) (row y) :=
  RepresentableKleisliConstraints.bent T u v x y

end ContextualComposition.GrothendieckStep.RepresentablePurePins
