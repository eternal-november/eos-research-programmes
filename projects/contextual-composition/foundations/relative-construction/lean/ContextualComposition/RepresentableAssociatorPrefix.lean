module
public import ContextualComposition.RepresentableKleisliConstraints
public import ContextualComposition.RepresentableStrictFold
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableAssociatorPrefix
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisliConstraints
open scoped CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
section Generic
variable {C : Type*} [Bicategory C] {a b c d e j w : C}
variable (f : a ⟶ b) (p : b ⟶ c) (m : c ⟶ d) (k : d ⟶ j) (n : j ⟶ w)
variable (h : c ⟶ e) (q : e ⟶ j) (r : e ⟶ j) (s : m ≫ k ≅ h ≫ q) (t : q ≫ n ≅ r ≫ n)
variable (l : b ⟶ j) (eq : (p ≫ h) ≫ r = l)
def word : ((((f ≫ p) ≫ m) ≫ k) ≫ n) ≅ (f ≫ l) ≫ n :=
  moveTail (f ≫ p) n s ≪≫ whiskerLeftIso ((f ≫ p) ≫ h) t ≪≫ moveHead f p h r n ≪≫
    eqToIso (congrArg (fun x => (f ≫ x) ≫ n) eq)
def body : (((p ≫ m) ≫ k) ≫ n) ≅ l ≫ n :=
  moveTail p n s ≪≫ whiskerLeftIso (p ≫ h) t ≪≫ (α_ (p ≫ h) r n).symm ≪≫
    whiskerRightIso (eqToIso eq) n
def frameIn : ((((f ≫ p) ≫ m) ≫ k) ≫ n) ≅ f ≫ (((p ≫ m) ≫ k) ≫ n) :=
  whiskerRightIso (whiskerRightIso (α_ f p m) k) n ≪≫
    whiskerRightIso (α_ f (p ≫ m) k) n ≪≫ (α_ f ((p ≫ m) ≫ k) n)
theorem factor : word f p m k n h q r s t l eq =
    frameIn f p m k n ≪≫ whiskerLeftIso f (body p m k n h q r s t l eq) ≪≫ (α_ f l n).symm := by
  unfold word frameIn body moveTail moveHead
  rw [← RepresentableStrictFold.castRight (congrArg (f ≫ ·) eq) n,
      ← RepresentableStrictFold.castLeft f eq]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, whiskerLeftIso_hom]
  bicategory
section Natural
variable {f f' : a ⟶ b} (x : f ⟶ f')
variable {z : b ⟶ w} (bdy : (((p ≫ m) ≫ k) ≫ n) ≅ l ≫ n)
def factored (f : a ⟶ b) :=
  frameIn f p m k n ≪≫ whiskerLeftIso f bdy ≪≫ (α_ f l n).symm
theorem natIn :
    (((x ▷ p) ▷ m) ▷ k) ▷ n ≫ (frameIn f' p m k n).hom =
    (frameIn f p m k n).hom ≫ x ▷ (((p ≫ m) ≫ k) ≫ n) := by
  have w1 := congrArg (fun t => (t ▷ k) ▷ n) (associator_naturality_left x p m)
  have w2 := congrArg (fun t => t ▷ n) (associator_naturality_left x (p ≫ m) k)
  simp only [comp_whiskerRight] at w1 w2
  simp only [frameIn,Iso.trans_hom,whiskerRightIso_hom,Category.assoc]
  rw [← Category.assoc ((((x ▷ p) ▷ m) ▷ k) ▷ n),w1,Category.assoc]
  rw [← Category.assoc (((x ▷ (p ≫ m)) ▷ k) ▷ n),w2,Category.assoc]
  rw [associator_naturality_left]
theorem natural :
    (((x ▷ p) ▷ m) ▷ k) ▷ n ≫ (factored p m k n l bdy f').hom =
    (factored p m k n l bdy f).hom ≫ (x ▷ l) ▷ n := by
  simp only [factored,Iso.trans_hom,whiskerLeftIso_hom,Iso.symm_hom,Category.assoc]
  rw [← Category.assoc (((x ▷ p) ▷ m) ▷ k ▷ n),natIn p m k n x,Category.assoc]
  rw [← Category.assoc (x ▷ (((p ≫ m) ≫ k) ≫ n)), ← whisker_exchange, Category.assoc]
  rw [associator_inv_naturality_left]
end Natural
end Generic
open AmbientBicategory AmbientHorizontalFrames AmbientHorizontalDiagrams AmbientCoherentPseudomonad
open RepresentableKleisli
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
variable {A D E J : B}
theorem first {f f' : KH S A D} (x : f ⟶ f') (g : KH S D E) :
    composeCell T x (𝟙 g) = (x ▷ K S g) ▷ M S (yObj E) T.mult := by
  change ((x ▷ K S g) ≫ f' ◁ (action S 1).map₂ (𝟙 g)) ▷ M S (yObj E) T.mult = _
  rw [(action S 1).map₂_id]
  change ((x ▷ K S g) ≫ f' ◁ (𝟙 (K S g))) ▷ M S (yObj E) T.mult = _
  rw [whiskerLeft_id,Category.comp_id]
noncomputable def tailBody (g : KH S D E) (h : KH S E J) :=
  body (K S g) (M S (yObj E) T.mult) (K S h) (M S (yObj J) T.mult) (K S (K S h))
    (M S (KObj S J) T.mult) (K S (M S (yObj J) T.mult))
    (squareM S T.mult h).symm (assocIso T (yObj J)) (K S (compose T g h)) (fold T g h).symm
set_option linter.defProp false in
def originalFrame (f : KH S A D) (g : KH S D E) (h : KH S E J) :=
  factor f (K S g) (M S (yObj E) T.mult) (K S h) (M S (yObj J) T.mult) (K S (K S h))
    (M S (KObj S J) T.mult) (K S (M S (yObj J) T.mult))
    (squareM S T.mult h).symm (assocIso T (yObj J)) (K S (compose T g h)) (fold T g h).symm
theorem original {f f' : KH S A D} (x : f ⟶ f') (g : KH S D E) (h : KH S E J) :
    composeCell T (composeCell T x (𝟙 g)) (𝟙 h) ≫ (reassociate T f' g h).hom =
    (reassociate T f g h).hom ≫ composeCell T x (𝟙 (compose T g h)) := by
  rw [first,first,first]
  have r1 : reassociate T f g h = factored (K S g) (M S (yObj E) T.mult) (K S h) (M S (yObj J) T.mult)
      (K S (compose T g h)) (tailBody T g h) f := originalFrame T f g h
  have r2 : reassociate T f' g h = factored (K S g) (M S (yObj E) T.mult) (K S h) (M S (yObj J) T.mult)
      (K S (compose T g h)) (tailBody T g h) f' := originalFrame T f' g h
  rw [r1,r2]
  exact natural _ _ _ _ _ x _
end ContextualComposition.GrothendieckStep.RepresentableAssociatorPrefix
