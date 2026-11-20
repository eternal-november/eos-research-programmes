module
public import ContextualComposition.RepresentableKleisliFunctor
public import ContextualComposition.RepresentableEndpointRealization
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliConstraints
open CategoryTheory CategoryTheory.Functor Opposite CategoryTheory.Bicategory
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli RepresentableEndpointRealization
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split}
variable {A D E J : B} (T : Data S)
noncomputable def leftUnit (f : KH S A D) : compose T (unit T A) f ≅ f :=
  whiskerRightIso (squareE S T.unit f).symm (M S (yObj D) T.mult) ≪≫
  (α_ f (AmbientHorizontalFrames.E S (KObj S D) T.unit) (M S (yObj D) T.mult)) ≪≫
  whiskerLeftIso f (leftIso T (yObj D)) ≪≫ (ρ_ f)
noncomputable def rightUnit (f : KH S A D) : compose T f (unit T D) ≅ f :=
  (α_ f (K S (unit T D)) (M S (yObj D) T.mult)) ≪≫ whiskerLeftIso f (rightIso T (yObj D)) ≪≫ (ρ_ f)
section Templates
variable {C : Type*} [Bicategory C] {a b c d e w : C}
def moveTail (p : a ⟶ b) {f : b ⟶ c} {g : c ⟶ d} {h : b ⟶ e} {k : e ⟶ d}
    (j : d ⟶ w) (s : f ≫ g ≅ h ≫ k) : ((p ≫ f) ≫ g) ≫ j ≅ (p ≫ h) ≫ (k ≫ j) :=
  whiskerRightIso ((α_ p f g) ≪≫ whiskerLeftIso p s ≪≫ (α_ p h k).symm) j ≪≫ (α_ (p ≫ h) k j)
def moveHead (f : a ⟶ b) (p : b ⟶ c) (g : c ⟶ d) (q : d ⟶ e) (h : e ⟶ w) :
    ((f ≫ p) ≫ g) ≫ (q ≫ h) ≅ (f ≫ ((p ≫ g) ≫ q)) ≫ h :=
  (α_ ((f ≫ p) ≫ g) q h).symm ≪≫
    whiskerRightIso ((α_ (f ≫ p) g q) ≪≫ (α_ f p (g ≫ q)) ≪≫ whiskerLeftIso f (α_ p g q).symm) h
end Templates
theorem fold (g : KH S D E) (h : KH S E J) :
    K S (compose T g h) = (K S g ≫ K S (K S h)) ≫ K S (M S (yObj J) T.mult) :=
  (AmbientBicategory.comp S 1 (g ≫ K S h) (M S (yObj J) T.mult)).trans
    (congrArg (· ≫ K S (M S (yObj J) T.mult)) (AmbientBicategory.comp S 1 g (K S h)))
noncomputable def reassociate (f : KH S A D) (g : KH S D E) (h : KH S E J) :
    compose T (compose T f g) h ≅ compose T f (compose T g h) :=
  moveTail (f ≫ K S g) (M S (yObj J) T.mult) (squareM S T.mult h).symm ≪≫
    whiskerLeftIso ((f ≫ K S g) ≫ K S (K S h)) (assocIso T (yObj J)) ≪≫
    moveHead f (K S g) (K S (K S h)) (K S (M S (yObj J) T.mult)) (M S (yObj J) T.mult) ≪≫
    eqToIso (congrArg (fun k => (f ≫ k) ≫ M S (yObj J) T.mult) (fold T g h).symm)
variable {A' D' : B}
noncomputable def preBend (u : A ⟶ A') (g : KH S A' D') :
    compose T (pureK T u) g ≅ target u g :=
  whiskerRightIso (α_ (pureMap u) (unit T A') (K S g)) (M S (yObj D') T.mult) ≪≫
  (α_ (pureMap u) (unit T A' ≫ K S g) (M S (yObj D') T.mult)) ≪≫
  whiskerLeftIso (pureMap u) (leftUnit T g)
noncomputable def postBend (v : D ⟶ D') (f : KH S A D) :
    compose T f (pureK T v) ≅ source v f :=
  eqToIso (congrArg (fun k => (f ≫ k) ≫ M S (yObj D') T.mult) (AmbientBicategory.comp S 1 (pureMap v) (unit T D'))) ≪≫
  whiskerRightIso (α_ f (K S (pureMap v)) (K S (unit T D'))).symm (M S (yObj D') T.mult) ≪≫
  rightUnit T (source v f)
noncomputable def bent (u : A ⟶ A') (v : D ⟶ D') (f : KH S A D) (g : KH S A' D') :
    (compose T f (pureK T v) ⟶ compose T (pureK T u) g) ≃ RepresentableNativeEndpoints.Square u v (row f) (row g) :=
  (across (postBend T v f) (preBend T u g)).trans (realization u v f g)
end ContextualComposition.GrothendieckStep.RepresentableKleisliConstraints
