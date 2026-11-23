module
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-! The bicategorical necessity argument for the empty frame. An actual pseudonatural parameter comparison acts on every native 2-cell. The argument needs its component at the empty object to be an equivalence, and the empty-framed pure map out of it to be an equivalence. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.EmptyFrameNecessity
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false

def retractEquivalence {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (E : A ⥤ B) (R : C ≌ D) (U : A ⥤ C) (V : B ⥤ D) (I : C ⥤ A) (J : D ⥤ B)
    (forward : E ⋙ V ≅ U ⋙ R.functor) (backward : R.functor ⋙ J ≅ I ⋙ E)
    (first : U ⋙ I ≅ 𝟭 A) (second : V ⋙ J ≅ 𝟭 B) : A ≌ B :=
  CategoryTheory.Equivalence.mk E (V ⋙ R.inverse ⋙ I)
    ((isoWhiskerRight forward (R.inverse ⋙ I) ≪≫ isoWhiskerLeft U (isoWhiskerRight R.unitIso.symm I) ≪≫ first).symm)
    (isoWhiskerLeft (V ⋙ R.inverse) backward.symm ≪≫ isoWhiskerLeft V (isoWhiskerRight R.counitIso J) ≪≫ second)

universe w v u
variable {B : Type u} [Bicategory.{w,v} B] {X Y : B}
variable (S : B ⥤ᵖ B) (θ : Pseudofunctor.StrongTrans S (Pseudofunctor.id B))

def naturalSquare (X Y : B) :
    S.mapFunctor X Y ⋙ postcomp (S.obj X) (θ.app Y) ≅ precomp Y (θ.app X) :=
  NatIso.ofComponents (fun f => θ.naturality f) (fun c => θ.naturality_naturality c)

def mapPost (e : X ⟶ Y) :
    postcomp X e ⋙ S.mapFunctor X Y ≅ S.mapFunctor X X ⋙ postcomp (S.obj X) (S.map e) :=
  NatIso.ofComponents (fun f => S.mapComp f e) (fun c => S.toOplax.mapComp_naturality_left c e)

def postEquivalence (A : B) (r : X ⟶ Y) (l : Y ⟶ X) (rl : r ≫ l ≅ 𝟙 X) (lr : l ≫ r ≅ 𝟙 Y) :
    (A ⟶ X) ≌ (A ⟶ Y) :=
  CategoryTheory.Equivalence.mk (postcomp A r) (postcomp A l)
    ((associatorNatIsoLeft A r l ≪≫ (postcomposing A X X).mapIso rl ≪≫ rightUnitorNatIso A X).symm)
    (associatorNatIsoLeft A l r ≪≫ (postcomposing A Y Y).mapIso lr ≪≫ rightUnitorNatIso A Y)

variable (k : X ⟶ S.obj X) (kθ : k ≫ θ.app X ≅ 𝟙 X)

def returnHom (Y : B) : (S.obj X ⟶ S.obj Y) ⥤ (X ⟶ Y) :=
  postcomp (S.obj X) (θ.app Y) ⋙ precomp Y k

def returnIso (Y : B) : S.mapFunctor X Y ⋙ returnHom S θ k Y ≅ 𝟭 (X ⟶ Y) :=
  isoWhiskerRight (naturalSquare S θ X Y) (precomp Y k) ≪≫
    (associatorNatIsoRight k (θ.app X) Y).symm ≪≫
    (precomposing X X Y).mapIso kθ ≪≫ leftUnitorNatIso X Y

def returnPost (e : X ⟶ Y) : postcomp (S.obj X) (S.map e) ⋙ returnHom S θ k Y ≅ returnHom S θ k X ⋙ postcomp X e := by
  let n : S.map e ≫ θ.app Y ≅ θ.app X ≫ e := θ.naturality e
  let U := postcomp (S.obj X) (θ.app X)
  unfold returnHom
  exact (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (associatorNatIsoLeft (S.obj X) (S.map e) (θ.app Y)) (precomp Y k) ≪≫
    isoWhiskerRight ((postcomposing (S.obj X) (S.obj X) Y).mapIso n) (precomp Y k) ≪≫
    isoWhiskerRight (associatorNatIsoLeft (S.obj X) (θ.app X) e).symm (precomp Y k) ≪≫
    Functor.associator U (postcomp (S.obj X) e) (precomp Y k) ≪≫
    isoWhiskerLeft U (associatorNatIsoMiddle k e).symm ≪≫
    (Functor.associator U (precomp X k) (postcomp X e)).symm

/-- Postcomposition by the original pure map is an equivalence on the full hom categories. The inverse and both natural isomorphisms are built from the parameter constraint and the action's compositor. -/
def necessary (e : X ⟶ Y) (l : S.obj Y ⟶ S.obj X) (rl : S.map e ≫ l ≅ 𝟙 _) (lr : l ≫ S.map e ≅ 𝟙 _) :
    (X ⟶ X) ≌ (X ⟶ Y) :=
  retractEquivalence (postcomp X e) (postEquivalence _ (S.map e) l rl lr)
    (S.mapFunctor X X) (S.mapFunctor X Y) (returnHom S θ k X) (returnHom S θ k Y)
    (mapPost S e) (returnPost S θ k e) (returnIso S θ k kθ X) (returnIso S θ k kθ Y)

theorem necessary_functor (e : X ⟶ Y) (l : S.obj Y ⟶ S.obj X)
    (rl : S.map e ≫ l ≅ 𝟙 _) (lr : l ≫ S.map e ≅ 𝟙 _) :
    (necessary S θ k kθ e l rl lr).functor = postcomp X e := rfl

end ContextualComposition.EmptyFrameNecessity
