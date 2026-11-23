module
public import ContextualComposition.RelativeTensorMixedLeftIdentity
public import ContextualComposition.RelativeTensorFourNative

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
variable {a d k : B}

set_option maxHeartbeats 120000 in
private theorem mixedLeftIdentityInsertion_rowFunctor :
    mixedLeftIdentityInsertion.{v,u} M N jM jN a d ⋙
      (identifyFirst (middleRow M N a) (column (middleComposite M N) d)).functor =
    CategoryTheory.Prod.sectR ((mixedUnitAt M N jM jN a a).obj (Discrete.mk (𝟙 a)))
      (Tensor (row M a) (column N d)) ⋙
      insertion (leftInner (row M a) N) (column (middleComposite M N) d) a := by
  unfold mixedLeftIdentityInsertion
  rw [Functor.assoc, middleRow_insertion]
  rfl
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a k d : B}

/-- Insert the second unit on the left and apply the supplied crossing. -/
def leftContactDomain (a k : B) :
    (row M a).obj ⟨k⟩ ⥤ Tensor (row M a) (column N k) :=
  CategoryTheory.Prod.sectR (nativeUnitValue jN (𝟙 a)) ((row M a).obj ⟨k⟩) ⋙
    insertion (row N a) (column M k) a ⋙ ((s.app ⟨k⟩).app ⟨op a⟩).toFunctor

/-- Insert the second unit on the right at the intermediate object. -/
def leftContactCodomain (a k : B) :
    (row M a).obj ⟨k⟩ ⥤ Tensor (row M a) (column N k) :=
  CategoryTheory.Prod.sectL ((row M a).obj ⟨k⟩) (nativeUnitValue jN (𝟙 k)) ⋙
    insertion (row M a) (column N k) k

/-- Insert the supplied native unit on the left and apply the native multiplication. -/
def leftNativeAbsorption (a k : B) : (row M a).obj ⟨k⟩ ⥤ (row M a).obj ⟨k⟩ :=
  CategoryTheory.Prod.sectR (nativeUnitValue jM (𝟙 a)) ((row M a).obj ⟨k⟩) ⋙
    insertion (row M a) (column M k) a ⋙ ((m.app ⟨k⟩).app ⟨op a⟩).toFunctor
end

section
/-- Paste the crossing contact and the actual rebracketing unit on a native
product category. The equalities are functor equalities, including maps. -/
private def pasteNativeLeftIdentity
    {X Y P E D C : Type*}
    [Category* X] [Category* Y] [Category* P] [Category* E] [Category* D] [Category* C]
    (U I : X × Y ⥤ C) (V : P × Y ⥤ E) (E₀ : D ≌ E) (Q : D ⥤ C)
    (G₀ G₁ : X ⥤ P) (W : X × Y ⥤ D) (L₁ : X ⥤ X) (L₂ : Y ⥤ Y)
    (source : U = (G₀.prod (𝟭 Y)) ⋙ V ⋙ E₀.inverse ⋙ Q)
    (contact : G₀ ≅ G₁)
    (decode : (G₁.prod (𝟭 Y)) ⋙ V = W ⋙ E₀.functor)
    (contract : W ⋙ Q = (L₁.prod L₂) ⋙ I)
    (left₁ : L₁ ≅ 𝟭 X) (left₂ : L₂ ≅ 𝟭 Y) : U ≅ I := by
  calc
    U ≅ (G₀.prod (𝟭 Y)) ⋙ V ⋙ E₀.inverse ⋙ Q := eqToIso source
    _ ≅ (G₁.prod (𝟭 Y)) ⋙ V ⋙ E₀.inverse ⋙ Q :=
      Functor.isoWhiskerRight (NatIso.prod contact (Iso.refl _)) _
    _ ≅ ((G₁.prod (𝟭 Y)) ⋙ V) ⋙ (E₀.inverse ⋙ Q) :=
      eqToIso (Functor.assoc _ _ _).symm
    _ ≅ (W ⋙ E₀.functor) ⋙ (E₀.inverse ⋙ Q) :=
      Functor.isoWhiskerRight (eqToIso decode) _
    _ ≅ (W ⋙ (E₀.functor ⋙ E₀.inverse)) ⋙ Q :=
      eqToIso (by rfl)
    _ ≅ (W ⋙ 𝟭 D) ⋙ Q :=
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft W E₀.unitIso.symm) Q
    _ ≅ W ⋙ Q := eqToIso (by rfl)
    _ ≅ (L₁.prod L₂) ⋙ I := eqToIso contract
    _ ≅ ((𝟭 X).prod (𝟭 Y)) ⋙ I := Functor.isoWhiskerRight (NatIso.prod left₁ left₂) I
    _ ≅ I := eqToIso (by rfl)
end

section
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB}
variable [Category.{vB} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})
variable {b : B} {c : B} {d : B}
variable {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
variable {n n' : (column N d).obj ⟨op c⟩} {y y' : Y.obj ⟨op d⟩}

set_option maxHeartbeats 130000 in
private theorem exposeMiddle_fourNative
    (f : x ⟶ x') (g : m ⟶ m') (h : n ⟶ n') (i : y ⟶ y') :
    (exposeMiddle X M N Y).functor.map
      ((insertR (leftInner X M) N Y c).map
       (productMap ((insertion X (column M c) b).map (productMap f g))
         ((insertM N Y c d).map (productMap h i)))) =
    (Reverse.insertL X (middleComposite M N) Y d).map
      (productMap ((insertion X (column (middleComposite M N) d) b).map
        (productMap f ((insertion (row M b) (column N d) c).map (productMap g h)))) i) := by
  have ha := associate_triple_native (leftInner X M) N Y
    ((insertion X (column M c) b).map (productMap f g)) h i
  have hz := restore_left_native (leftInner X M) N Y
    ((insertion X (column M c) b).map (productMap f g) |> fun k =>
      (insertion (leftInner X M) (column N d) c).map (productMap k h)) i
  dsimp only [exposeMiddle, CategoryTheory.Equivalence.trans, CategoryTheory.Equivalence.symm, Functor.comp_map]
  change (firstPentagonEdge X M N Y).map
    ((Reverse.unassociate (leftInner X M) N Y).map
      ((insertR (leftInner X M) N Y c).map
        (productMap ((insertion X (column M c) b).map (productMap f g))
          ((insertM N Y c d).map (productMap h i))))) = _
  erw [← ha, associate_native, hz]
  unfold firstPentagonEdge
  erw [First.on_native]
  change (Reverse.insertL X (middleComposite M N) Y d).map
    (productMap ((associate X M (column N d)).map _) i) = _
  erw [associate_triple_native X M (column N d)]
  rfl
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (jN : unitModule B ⟶ N)
variable {a k d : B}

private def nativeLeftPayload (P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v})) (a k d : B) :
    (Tensor (row P a) (column Q k) × (column N d).obj ⟨op k⟩) ⥤ innerLeft (row M a) P Q (column N d) :=
  ((CategoryTheory.Prod.sectR (nativeUnitValue jM (𝟙 a)) (Tensor (row P a) (column Q k)) ⋙
    insertion (row M a) (column (middleComposite P Q) k) a).prod (𝟭 _)) ⋙
    Reverse.insertL (row M a) (middleComposite P Q) (column N d) k

private def nativeLeftOpposedTarget (a k d : B) :
    ((row M a).obj ⟨k⟩ × (column N d).obj ⟨op k⟩) ⥤ opposedPairs (row M a) M N (column N d) :=
  ((CategoryTheory.Prod.sectR (nativeUnitValue jM (𝟙 a)) ((row M a).obj ⟨k⟩) ⋙
    insertion (row M a) (column M k) a).prod
   (CategoryTheory.Prod.sectR (nativeUnitValue jN (𝟙 k)) ((column N d).obj ⟨op k⟩) ⋙
    insertion (row N k) (column N d) k)) ⋙
    insertion (leftInner (row M a) M) (rightInner N (column N d)) k

set_option maxHeartbeats 140000 in
private theorem nativeLeft_decodeFunctor :
    nativeLeftOpposedTarget.{v,u} M N jM jN a k d ⋙ (exposeMiddle (row M a) M N (column N d)).functor =
    ((leftContactCodomain.{v,u} M N jN a k).prod (𝟭 ((column N d).obj ⟨op k⟩))) ⋙
      nativeLeftPayload.{v,u} M N jM M N a k d := by
  fapply Functor.ext
  · rintro ⟨p,q⟩
    rfl
  · rintro ⟨p,q⟩ ⟨p',q'⟩ ⟨f,g⟩
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    simp only [nativeLeftOpposedTarget, nativeLeftPayload, leftContactCodomain, Functor.prod_map,
      Functor.comp_map, CategoryTheory.Prod.sectR_map, CategoryTheory.Prod.sectL_map, Functor.id_map]
    exact exposeMiddle_fourNative (row M a) M N (column N d)
      (𝟙 (nativeUnitValue jM (𝟙 a))) f (𝟙 (nativeUnitValue jN (𝟙 k))) g
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a k d : B}

private theorem transportAppNative
    {C : Type*} [Category* C]
    {F F' G : LocallyDiscrete C ⥤ᵖ Cat} (h : F = F') (s : F ⟶ G) (j : LocallyDiscrete C) :
    HEq ((Eq.mp (congrArg (fun P => P ⟶ G) h) s).app j) (s.app j) := by
  cases h
  rfl

private theorem rowMultiplication_nativeApp :
    (rowMultiplication.{max u v,u,max u v,max u v} M m a).app ⟨k⟩ = (m.app ⟨k⟩).app ⟨op a⟩ := by
  apply eq_of_heq
  exact transportAppNative (middleRow M M a) (rowMap m a) ⟨k⟩

section Generic
universe b c f g
variable {D : Type b} [Category.{c} D]
variable {A A' : LocallyDiscrete D ⥤ᵖ Cat.{f,g}}
variable {Z Z' : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{f,g}}
private theorem mapBoth_insertionFunctor (S : A ⟶ A') (T : Z ⟶ Z') (i : D) :
    insertion A Z i ⋙ mapBoth S T =
    ((First.part S i).prod (Second.part T i)) ⋙ insertion A' Z' i := by
  fapply Functor.ext
  · rintro ⟨p,q⟩
    rfl
  · rintro ⟨p,q⟩ ⟨p',q'⟩ ⟨f,g⟩
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id,Functor.comp_map,Functor.prod_map]
    exact mapBoth_native S T f g
end Generic

set_option maxHeartbeats 140000 in
private theorem mixedLeft_contractionFunctor :
    insertion (leftInner (row M a) M) (rightInner N (column N d)) k ⋙
      mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩) =
    (((m.app ⟨k⟩).app ⟨op a⟩).toFunctor.prod (((n.app ⟨d⟩).app ⟨op k⟩).toFunctor)) ⋙
      insertion (row M a) (column N d) k := by
  let F := rowMultiplication.{max u v,u,max u v,max u v} M m a
  let G := n.app ⟨d⟩
  let H := First.part F k
  let K := Second.part G k
  let I := insertion (row M a) (column N d) k
  have h := mapBoth_insertionFunctor F G k
  have hComp : H = ((m.app ⟨k⟩).app ⟨op a⟩).toFunctor :=
    congrArg Cat.Hom.toFunctor (rowMultiplication_nativeApp M m (a := a) (k := k))
  exact h.trans (congrArg (fun U => (U.prod K) ⋙ I) hComp)
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (jN : unitModule B ⟶ N)
variable {a k d : B}

private def leftContactBefore (a k : B) :
    (row M a).obj ⟨k⟩ ⥤ Tensor (row N a) (column M k) :=
  CategoryTheory.Prod.sectR (nativeUnitValue jN (𝟙 a)) ((row M a).obj ⟨k⟩) ⋙
    insertion (row N a) (column M k) a

private def nativeLeftOpposedSource (a k d : B) :
    ((row M a).obj ⟨k⟩ × (column N d).obj ⟨op k⟩) ⥤ opposedPairs (row M a) N M (column N d) :=
  insertion (row M a) (column N d) k ⋙
    CategoryTheory.Prod.sectR
      ((insertion (row M a) (column N a) a).obj (nativeUnitValue jM (𝟙 a),nativeUnitValue jN (𝟙 a)))
      (Tensor (row M a) (column N d)) ⋙
    insertion (leftInner (row M a) N) (rightInner M (column N d)) a

set_option maxHeartbeats 125000 in
private theorem nativeLeft_rowSource :
    insertion (row M a) (column N d) k ⋙
      (mixedLeftIdentityInsertion.{v,u} M N jM jN a d ⋙
        (identifyFirst (middleRow M N a) (column (middleComposite M N) d)).functor) =
      nativeLeftOpposedSource.{v,u} M N jM jN a k d := by
  rw [mixedLeftIdentityInsertion_rowFunctor]
  rw [mixedUnitAt_obj]
  rfl

set_option maxHeartbeats 170000 in
private theorem nativeLeft_exposeSource :
    nativeLeftOpposedSource.{v,u} M N jM jN a k d ⋙
      (exposeMiddle (row M a) N M (column N d)).functor =
    ((leftContactBefore.{v,u} M N jN a k).prod (𝟭 ((column N d).obj ⟨op k⟩))) ⋙
      nativeLeftPayload.{v,u} M N jM N M a k d := by
  fapply Functor.ext
  · rintro ⟨p,q⟩
    rfl
  · rintro ⟨p,q⟩ ⟨p',q'⟩ ⟨f,g⟩
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    simp only [nativeLeftOpposedSource, nativeLeftPayload, leftContactBefore, Functor.prod_map,
      Functor.comp_map, CategoryTheory.Prod.sectR_map, Functor.id_map]
    have h := exposeMiddle_fourNative (row M a) N M (column N d)
      (𝟙 (nativeUnitValue jM (𝟙 a))) (𝟙 (nativeUnitValue jN (𝟙 a))) f g
    have hUnit : productMap (𝟙 (nativeUnitValue jM (𝟙 a))) (𝟙 (nativeUnitValue jN (𝟙 a))) =
        𝟙 (nativeUnitValue jM (𝟙 a), nativeUnitValue jN (𝟙 a)) := rfl
    rw [hUnit] at h
    simpa only [Functor.map_id] using h
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable {a k d : B}

set_option maxHeartbeats 125000 in
private theorem nativeLeft_crossExpose :
    nativeLeftPayload.{v,u} M N jM N M a k d ⋙
      mapFirst (G := column N d) (liftCrossing (row M a) M N s) =
    ((((s.app ⟨k⟩).app ⟨op a⟩).toFunctor).prod (𝟭 ((column N d).obj ⟨op k⟩))) ⋙
      nativeLeftPayload.{v,u} M N jM M N a k d := by
  fapply Functor.ext
  · rintro ⟨p,q⟩
    rfl
  · rintro ⟨p,q⟩ ⟨p',q'⟩ ⟨f,g⟩
    simp only [eqToHom_refl,Category.id_comp,Category.comp_id]
    simp only [nativeLeftPayload,Functor.prod_map,Functor.comp_map,CategoryTheory.Prod.sectR_map,Functor.id_map]
    exact exposedCrossing_native (row M a) M N (column N d) s (𝟙 (nativeUnitValue jM (𝟙 a))) f g
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (jN : unitModule B ⟶ N)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a k d : B}

private theorem NativeLeftContractBoundaryproductFunctorComp
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    (G : A ⥤ B) (H : C ⥤ D) (J : B ⥤ E) (K : D ⥤ F) :
    (G.prod H) ⋙ (J.prod K) = (G ⋙ J).prod (H ⋙ K) := rfl

set_option maxHeartbeats 200000 in
private theorem nativeLeft_contractBoundary :
    nativeLeftOpposedTarget.{v,u} M N jM jN a k d ⋙
      mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩) =
    ((leftNativeAbsorption.{v,u} M jM m a k).prod (leftNativeAbsorption.{v,u} N jN n k d)) ⋙
      insertion (row M a) (column N d) k := by
  let L := CategoryTheory.Prod.sectR (nativeUnitValue jM (𝟙 a)) ((row M a).obj ⟨k⟩) ⋙
    insertion (row M a) (column M k) a
  let R := CategoryTheory.Prod.sectR (nativeUnitValue jN (𝟙 k)) ((column N d).obj ⟨op k⟩) ⋙
    insertion (row N k) (column N d) k
  let J := insertion (leftInner (row M a) M) (rightInner N (column N d)) k
  let Q := mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)
  let F := ((m.app ⟨k⟩).app ⟨op a⟩).toFunctor
  let G := ((n.app ⟨d⟩).app ⟨op k⟩).toFunctor
  let I := insertion (row M a) (column N d) k
  have h := mixedLeft_contractionFunctor.{v,u} M N m n (a:=a) (k:=k) (d:=d)
  calc
    _ = (L.prod R) ⋙ J ⋙ Q := (Functor.assoc _ _ _)
    _ = (L.prod R) ⋙ ((F.prod G) ⋙ I) := congrArg (fun y => (L.prod R) ⋙ y) h
    _ = ((L.prod R) ⋙ F.prod G) ⋙ I := (Functor.assoc _ _ _).symm
    _ = ((L ⋙ F).prod (R ⋙ G)) ⋙ I :=
      congrArg (fun y => y ⋙ I) (NativeLeftContractBoundaryproductFunctorComp L R F G)
    _ = _ := by rfl
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (jN : unitModule B ⟶ N)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a k d : B}


private theorem exactSixAssoc
    {C₀ C₁ C₂ C₃ C₄ C₅ C₆ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* C₄] [Category* C₅] [Category* C₆]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (I : C₃ ⥤ C₄) (J : C₄ ⥤ C₅) (K : C₅ ⥤ C₆) :
    F ⋙ G ⋙ (H ⋙ I ⋙ J) ⋙ K = F ⋙ G ⋙ H ⋙ I ⋙ J ⋙ K := by rfl

set_option maxHeartbeats 80000 in
private theorem mixedLeftIdentityComposite_functor :
    mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d =
    mixedLeftIdentityInsertion.{v,u} M N jM jN a d ⋙
      (identifyFirst (middleRow M N a) (column (middleComposite M N) d)).functor ⋙
      (exposeMiddle (row M a) N M (column N d)).functor ⋙
      mapFirst (G := column N d) (liftCrossing (row M a) M N s) ⋙
      (exposeMiddle (row M a) M N (column N d)).inverse ⋙
      mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩) := by
  unfold mixedLeftIdentityComposite mixedMultiplicationAt crossMiddle
  let F := mixedLeftIdentityInsertion.{v,u} M N jM jN a d
  let G := (identifyFirst (middleRow M N a) (column (middleComposite M N) d)).functor
  let H := (exposeMiddle (row M a) N M (column N d)).functor
  let I := mapFirst (G := column N d) (liftCrossing (row M a) M N s)
  let J := (exposeMiddle (row M a) M N (column N d)).inverse
  let K := mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)
  exact exactSixAssoc F G H I J K
end

section
private theorem pasteNativeSourceBoundary
    {A B C D E H J K P P' : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    [Category* H] [Category* J] [Category* K] [Category* P] [Category* P']
    (I : A ⥤ B) (F : B ⥤ K)
    (U : B ⥤ C) (R : C ⥤ D) (T : D ⥤ E) (X : E ⥤ H) (V : H ⥤ J) (Q : J ⥤ K)
    (W : A ⥤ D) (G : A ⥤ P) (V₀ : P ⥤ E) (S : P ⥤ P') (V₁ : P' ⥤ H) (G₁ : A ⥤ P')
    (hF : F = U ⋙ R ⋙ T ⋙ X ⋙ V ⋙ Q)
    (hr : I ⋙ (U ⋙ R) = W)
    (he : W ⋙ T = G ⋙ V₀)
    (hx : V₀ ⋙ X = S ⋙ V₁)
    (ht : G ⋙ S = G₁) :
    I ⋙ F = G₁ ⋙ V₁ ⋙ V ⋙ Q := by
  calc
    _ = I ⋙ U ⋙ R ⋙ T ⋙ X ⋙ V ⋙ Q := congrArg (I ⋙ ·) hF
    _ = (I ⋙ (U ⋙ R)) ⋙ T ⋙ X ⋙ V ⋙ Q := by rfl
    _ = W ⋙ T ⋙ X ⋙ V ⋙ Q := congrArg (· ⋙ T ⋙ X ⋙ V ⋙ Q) hr
    _ = (W ⋙ T) ⋙ X ⋙ V ⋙ Q := by rfl
    _ = (G ⋙ V₀) ⋙ X ⋙ V ⋙ Q := congrArg (· ⋙ X ⋙ V ⋙ Q) he
    _ = G ⋙ (V₀ ⋙ X) ⋙ V ⋙ Q := by rfl
    _ = G ⋙ (S ⋙ V₁) ⋙ V ⋙ Q := congrArg (fun F' => G ⋙ F' ⋙ V ⋙ Q) hx
    _ = (G ⋙ S) ⋙ V₁ ⋙ V ⋙ Q := by rfl
    _ = _ := congrArg (· ⋙ V₁ ⋙ V ⋙ Q) ht
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (jN : unitModule B ⟶ N)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a k d : B}

private theorem NativeLeftSourceBoundaryGenericproductFunctorComp
    {A B C D E F : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    (G : A ⥤ B) (H : C ⥤ D) (J : B ⥤ E) (K : D ⥤ F) :
    (G.prod H) ⋙ (J.prod K) = (G ⋙ J).prod (H ⋙ K) := rfl

set_option maxHeartbeats 300000 in
private theorem nativeLeft_sourceBoundary :
    insertion (row M a) (column N d) k ⋙ mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d =
    ((leftContactDomain.{v,u} M N jN s a k).prod (𝟭 ((column N d).obj ⟨op k⟩))) ⋙
      nativeLeftPayload.{v,u} M N jM M N a k d ⋙
      (exposeMiddle (row M a) M N (column N d)).inverse ⋙
      mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩) := by
  let I := insertion (row M a) (column N d) k
  let R := (identifyFirst (middleRow M N a) (column (middleComposite M N) d)).functor
  let U := mixedLeftIdentityInsertion.{v,u} M N jM jN a d
  let E := (exposeMiddle (row M a) N M (column N d)).functor
  let X := mapFirst (G := column N d) (liftCrossing (row M a) M N s)
  let V := (exposeMiddle (row M a) M N (column N d)).inverse
  let Q := mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)
  let W := nativeLeftOpposedSource.{v,u} M N jM jN a k d
  let Y := (column N d).obj ⟨op k⟩
  let J := (leftContactBefore.{v,u} M N jN a k).prod (𝟭 Y)
  let V₀ := nativeLeftPayload.{v,u} M N jM N M a k d
  let V₁ := nativeLeftPayload.{v,u} M N jM M N a k d
  let S := (((s.app ⟨k⟩).app ⟨op a⟩).toFunctor).prod (𝟭 Y)
  have ha := mixedLeftIdentityComposite_functor.{v,u} M N jM jN s m n (a:=a) (d:=d)
  have hr := nativeLeft_rowSource.{v,u} M N jM jN (a:=a) (k:=k) (d:=d)
  have he := nativeLeft_exposeSource.{v,u} M N jM jN (a:=a) (k:=k) (d:=d)
  have hx := nativeLeft_crossExpose.{v,u} M N jM s (a:=a) (k:=k) (d:=d)
  have ht : J ⋙ S = (leftContactDomain.{v,u} M N jN s a k).prod (𝟭 Y) := by
    calc
      _ = ((leftContactBefore.{v,u} M N jN a k) ⋙ ((s.app ⟨k⟩).app ⟨op a⟩).toFunctor).prod
          ((𝟭 Y) ⋙ (𝟭 Y)) := NativeLeftSourceBoundaryGenericproductFunctorComp _ _ _ _
      _ = _ := congrArg (fun F => (leftContactDomain.{v,u} M N jN s a k).prod F) (Functor.id_comp _)
  let A := (row M a).obj ⟨k⟩ × (column N d).obj ⟨op k⟩
  let B' := Tensor (row M a) (column N d)
  let C := Tensor (row (middleComposite M N) a) (column (middleComposite M N) d)
  let D := opposedPairs (row M a) N M (column N d)
  let C₁ := innerLeft (row M a) N M (column N d)
  let C₂ := innerLeft (row M a) M N (column N d)
  let C₃ := opposedPairs (row M a) M N (column N d)
  let P := Tensor (row N a) (column M k) × Y
  let P' := Tensor (row M a) (column N k) × Y
  let F := mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d
  let G₁ := (leftContactDomain.{v,u} M N jN s a k).prod (𝟭 Y)
  exact pasteNativeSourceBoundary (A := A) (B := B') (C := C) (D := D)
    (E := C₁) (H := C₂) (J := C₃) (K := B') (P := P) (P' := P')
    I F U R E X V Q W J V₀ S V₁ G₁ ha hr he hx ht
end

section
universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M)
variable (jN : unitModule B ⟶ N)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
variable {a k d : B}

set_option maxHeartbeats 240000 in
/-- Naturality of the mixed left-unit comparison on one native product, before descent along balances. -/
@[no_expose]
noncomputable def mixedLeftIdentityOnNativeProduct
    (contact : leftContactDomain.{v,u} M N jN s a k ≅ leftContactCodomain.{v,u} M N jN a k)
    (left₁ : leftNativeAbsorption.{v,u} M jM m a k ≅ 𝟭 _)
    (left₂ : leftNativeAbsorption.{v,u} N jN n k d ≅ 𝟭 _) :
    insertion (row M a) (column N d) k ⋙ mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d ≅
    insertion (row M a) (column N d) k := by
  let I := insertion (row M a) (column N d) k
  let U := I ⋙ mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d
  let P := nativeLeftPayload.{v,u} M N jM M N a k d
  let E := exposeMiddle (row M a) M N (column N d)
  let Q := mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)
  let G₀ := leftContactDomain.{v,u} M N jN s a k
  let G₁ := leftContactCodomain.{v,u} M N jN a k
  let W := nativeLeftOpposedTarget.{v,u} M N jM jN a k d
  let L₁ := leftNativeAbsorption.{v,u} M jM m a k
  let L₂ := leftNativeAbsorption.{v,u} N jN n k d
  have hS := nativeLeft_sourceBoundary.{v,u} M N jM jN s m n (a := a) (k := k) (d := d)
  have hD := (nativeLeft_decodeFunctor.{v,u} M N jM jN (a := a) (k := k) (d := d)).symm
  have hC := nativeLeft_contractBoundary.{v,u} M N jM jN m n (a := a) (k := k) (d := d)
  exact pasteNativeLeftIdentity (X := (row M a).obj ⟨k⟩) (Y := (column N d).obj ⟨op k⟩)
    (P := Tensor (row M a) (column N k)) (E := innerLeft (row M a) M N (column N d))
    (D := opposedPairs (row M a) M N (column N d)) (C := Tensor (row M a) (column N d))
    U I P E Q G₀ G₁ W L₁ L₂ hS contact hD hC left₁ left₂
end

end ContextualComposition.RelativeTensor.Iterated
