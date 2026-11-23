module
public import ContextualComposition.RelativeTensorMixedStrongUnit
public import ContextualComposition.RelativeTensorMiddleRowGenerators

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

universe v u
variable {B : Type u} [Category.{max u v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
variable (s : middleComposite N M ⟶ middleComposite M N)
variable (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
local notation "H" => middleComposite M N

/-- Insert a left unit object using the actual unit and tensor of the mixed algebra candidate. -/
def mixedLeftIdentityInsertion (a d : B) : (column H d).obj ⟨op a⟩ ⥤
    (column (middleComposite H H) d).obj ⟨op a⟩ :=
  CategoryTheory.Prod.sectR ((mixedUnitAt M N jM jN a a).obj (Discrete.mk (𝟙 a)))
      ((column H d).obj ⟨op a⟩) ⋙
    insertion (row H a) (column H d) a

set_option maxHeartbeats 100000 in
private theorem mixedLeftIdentityInsertion_obj (a d : B) (z : Tensor (row M a) (column N d)) :
    (mixedLeftIdentityInsertion.{v,u} M N jM jN a d).obj z =
      (insertion (row H a) (column H d) a).obj
        ((mixedUnitAt M N jM jN a a).obj (Discrete.mk (𝟙 a)), z) := rfl

set_option maxHeartbeats 100000 in
private theorem mixedLeftIdentityInsertion_row (a d : B) (z : Tensor (row M a) (column N d)) :
    (identifyFirst (middleRow M N a) (column H d)).functor.obj
      ((mixedLeftIdentityInsertion.{v,u} M N jM jN a d).obj z) =
      (insertion (leftInner (row M a) N) (column H d) a).obj
        ((mixedUnitAt M N jM jN a a).obj (Discrete.mk (𝟙 a)), z) :=
  middleRow_object M N (column H d) a a
    ((mixedUnitAt M N jM jN a a).obj (Discrete.mk (𝟙 a))) z

variable {a k d : B}
variable (x : (row M a).obj ⟨k⟩) (y : (column N d).obj ⟨op k⟩)

abbrev innerBefore := (insertion (row N a) (column M k) a).obj
  (nativeUnitValue jN (𝟙 a),x)
abbrev innerAfter := (insertion (row M a) (column N k) k).obj
  (x,nativeUnitValue jN (𝟙 k))

private abbrev exposedVertex
    (P Q : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v,max u v}))
    {i j : B} (q : (column (middleComposite P Q) j).obj ⟨op i⟩)
    (r : (row M a).obj ⟨i⟩) (w : (column N d).obj ⟨op j⟩) :
      innerLeft (row M a) P Q (column N d) :=
  (insertion (leftInner (row M a) (middleComposite P Q)) (column N d) j).obj
    ((insertion (row M a) (column (middleComposite P Q) j) i).obj (r,q),w)

private abbrev nativeMixedUnit : Tensor (row M a) (column N a) :=
  (insertion (row M a) (column N a) a).obj
    (nativeUnitValue jM (𝟙 a), nativeUnitValue jN (𝟙 a))

abbrev nativeRetained : Tensor (row M a) (column N d) :=
  (insertion (row M a) (column N d) k).obj (x,y)

private abbrev nativeAfterRow : opposedPairs (row M a) N M (column N d) :=
  (insertion (leftInner (row M a) N) (column H d) a).obj
    (nativeMixedUnit M N jM jN (a := a), nativeRetained M N x y)

set_option maxHeartbeats 160000 in
private theorem leftInput_nativeExposure :
    ((exposeMiddle (row M a) N M (column N d)).functor.obj
      (nativeAfterRow M N jM jN x y)) =
    exposedVertex M N N M (innerBefore M N jN x) (nativeUnitValue jM (𝟙 a)) y := by
  rfl

set_option maxHeartbeats 180000 in
private theorem leftInput_exposed
    (z : Tensor (row M a) (column N d)) (hz : z = nativeRetained M N x y) :
    ((exposeMiddle (row M a) N M (column N d)).functor.obj
      ((identifyFirst (middleRow M N a) (column H d)).functor.obj
        ((mixedLeftIdentityInsertion.{v,u} M N jM jN a d).obj z))) =
    exposedVertex M N N M (innerBefore M N jN x) (nativeUnitValue jM (𝟙 a)) y := by
  let K := (exposeMiddle (row M a) N M (column N d)).functor
  let J := insertion (leftInner (row M a) N) (column H d) a
  let W : Tensor (row M a) (column N a) := (mixedUnitAt M N jM jN a a).obj (Discrete.mk (𝟙 a))
  let W' := nativeMixedUnit M N jM jN (a := a)
  have hW : W = W' := mixedUnitAt_obj M N jM jN (𝟙 a)
  have hr := mixedLeftIdentityInsertion_row M N jM jN a d z
  have hp := congrArg₂ (fun (q : Tensor (row M a) (column N a))
    (r : Tensor (row M a) (column N d)) => J.obj (q,r)) hW hz
  exact ((congrArg K.obj hr).trans (congrArg K.obj hp)).trans (leftInput_nativeExposure M N jM jN x y)

set_option maxHeartbeats 500000 in
private theorem leftInput_crossed :
    (mapFirst (G := column N d) (liftCrossing (row M a) M N s)).obj
      (exposedVertex M N N M (innerBefore M N jN x) (nativeUnitValue jM (𝟙 a)) y) =
    exposedVertex M N M N (((s.app ⟨k⟩).app ⟨op a⟩).toFunctor.obj (innerBefore M N jN x))
      (nativeUnitValue jM (𝟙 a)) y := by
  rfl

abbrev rowInputM :=
  (insertion (row M a) (column M k) a).obj (nativeUnitValue jM (𝟙 a), x)

abbrev rowInputN :=
  (insertion (row N k) (column N d) k).obj (nativeUnitValue jN (𝟙 k), y)

private abbrev opposedTarget : opposedPairs (row M a) M N (column N d) :=
  (insertion (leftInner (row M a) M) (rightInner N (column N d)) k).obj
    (rowInputM M jM x, rowInputN N jN y)

set_option maxHeartbeats 500000 in
private theorem leftInput_expose_target :
    ((exposeMiddle (row M a) M N (column N d)).functor.obj
      (opposedTarget M N jM jN x y)) =
    exposedVertex M N M N (innerAfter M N jN x) (nativeUnitValue jM (𝟙 a)) y := by
  rfl

private theorem transportApp
    {C : Type*} [Category* C]
    {F F' G : LocallyDiscrete C ⥤ᵖ Cat} (h : F = F') (s : F ⟶ G) (j : LocallyDiscrete C) :
    HEq ((Eq.mp (congrArg (fun P => P ⟶ G) h) s).app j) (s.app j) := by
  cases h
  rfl

set_option maxHeartbeats 400000 in
private theorem rowMultiplication_component :
    (rowMultiplication.{max u v,u,max u v,max u v} M m a).app ⟨k⟩ = (m.app ⟨k⟩).app ⟨op a⟩ := by
  apply eq_of_heq
  exact transportApp (middleRow M M a) (rowMap m a) ⟨k⟩

set_option maxHeartbeats 500000 in
private theorem leftInput_contract_target :
    (mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)).obj (opposedTarget M N jM jN x y) =
    (insertion (row M a) (column N d) k).obj
      (((m.app ⟨k⟩).app ⟨op a⟩).toFunctor.obj (rowInputM M jM x),
       ((n.app ⟨d⟩).app ⟨op k⟩).toFunctor.obj (rowInputN N jN y)) := by
  change (insertion (row M a) (column N d) k).obj
    (((rowMultiplication.{max u v,u,max u v,max u v} M m a).app ⟨k⟩).toFunctor.obj (rowInputM M jM x),
      ((n.app ⟨d⟩).app ⟨op k⟩).toFunctor.obj (rowInputN N jN y)) = _
  rw [rowMultiplication_component M m (a := a) (k := k)]


/-- The actual multiplication after insertion of the supplied unit. -/
noncomputable def mixedLeftIdentityComposite (a d : B) :
    Tensor (row M a) (column N d) ⥤ Tensor (row M a) (column N d) :=
  mixedLeftIdentityInsertion.{v,u} M N jM jN a d ⋙
    mixedMultiplicationAt.{max u v,u,max u v,max u v,max u v,max u v} M N s m n a d

set_option maxHeartbeats 120000 in
private theorem mixedLeftIdentityComposite_stages (z : Tensor (row M a) (column N d)) :
    (mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d).obj z =
    (mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)).obj
      ((exposeMiddle (row M a) M N (column N d)).inverse.obj
        ((mapFirst (G := column N d) (liftCrossing (row M a) M N s)).obj
          ((exposeMiddle (row M a) N M (column N d)).functor.obj
            ((identifyFirst (middleRow M N a) (column H d)).functor.obj
              ((mixedLeftIdentityInsertion.{v,u} M N jM jN a d).obj z))))) := by
  simp only [mixedLeftIdentityComposite, mixedMultiplicationAt, crossMiddle, Functor.comp_obj]

set_option maxHeartbeats 120000 in
/-- The actual functor fixing the outer native unit and second payload. -/
private def fixedPayload (y : (column N d).obj ⟨op k⟩) :
    (column (middleComposite M N) k).obj ⟨op a⟩ ⥤
      innerLeft (row M a) M N (column N d) :=
  CategoryTheory.Prod.sectR (nativeUnitValue jM (𝟙 a)) _ ⋙
    insertion (row M a) (column (middleComposite M N) k) a ⋙
      CategoryTheory.Prod.sectL _ y ⋙
        insertion (leftInner (row M a) (middleComposite M N)) (column N d) k

set_option maxHeartbeats 150000 in
private theorem fixedPayload_obj (q : (column (middleComposite M N) k).obj ⟨op a⟩) :
    (fixedPayload M N jM y).obj q =
    exposedVertex M N M N q (nativeUnitValue jM (𝟙 a)) y := by
  simp only [fixedPayload, exposedVertex, Functor.comp_obj, CategoryTheory.Prod.sectL_obj, CategoryTheory.Prod.sectR_obj]

set_option maxHeartbeats 160000 in
private theorem nativeDecoded :
    (exposeMiddle (row M a) M N (column N d)).functor.obj
      (opposedTarget M N jM jN x y) =
    (fixedPayload M N jM y).obj (innerAfter M N jN x) :=
  (leftInput_expose_target M N jM jN x y).trans
    (fixedPayload_obj M N jM y (innerAfter M N jN x)).symm


set_option maxHeartbeats 240000 in
private theorem nativeBefore
    (z : Tensor (row M a) (column N d)) (hz : z = nativeRetained M N x y) :
    (mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d).obj z =
    (mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)).obj
      ((exposeMiddle (row M a) M N (column N d)).inverse.obj
        ((fixedPayload M N jM y).obj
          (((s.app ⟨k⟩).app ⟨op a⟩).toFunctor.obj (innerBefore M N jN x)))) := by
  let X := mapFirst (G := column N d) (liftCrossing (row M a) M N s)
  let D := (exposeMiddle (row M a) M N (column N d)).inverse
  let Q := mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)
  let q₀ := ((s.app ⟨k⟩).app ⟨op a⟩).toFunctor.obj (innerBefore M N jN x)
  have h₀ := mixedLeftIdentityComposite_stages M N jM jN s m n z
  have h₁ := congrArg X.obj (leftInput_exposed M N jM jN x y z hz)
  have h₂ := leftInput_crossed M N jM jN s x y
  have h₃ := (fixedPayload_obj M N jM y q₀).symm
  exact h₀.trans (congrArg (fun q => Q.obj (D.obj q)) ((h₁.trans h₂).trans h₃))

set_option maxHeartbeats 240000 in
/-- A left-unit comparison at a retained object with supplied native coordinates. -/
@[no_expose]
noncomputable def mixedLeftIdentityAt
    (z : Tensor (row M a) (column N d)) (hz : z = nativeRetained M N x y)
    (contact : ((s.app ⟨k⟩).app ⟨op a⟩).toFunctor.obj
      (innerBefore M N jN x) ≅ innerAfter M N jN x)
    (leftM : ((m.app ⟨k⟩).app ⟨op a⟩).toFunctor.obj
      (rowInputM M jM x) ≅ x)
    (leftN : ((n.app ⟨d⟩).app ⟨op k⟩).toFunctor.obj
      (rowInputN N jN y) ≅ y) :
    (mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d).obj z ≅ z := by
  let V := fixedPayload M N jM (a := a) y
  let E := exposeMiddle (row M a) M N (column N d)
  let Q := mapBoth (rowMultiplication.{max u v,u,max u v,max u v} M m a) (n.app ⟨d⟩)
  let w := opposedTarget M N jM jN x y
  let I := insertion (row M a) (column N d) k
  have hBefore := nativeBefore M N jM jN s m n x y z hz
  have hDecoded := nativeDecoded M N jM jN x y
  have hContract := leftInput_contract_target M N jM jN m n x y
  let e₀ := eqToIso hBefore
  let e₁ := Q.mapIso (E.inverse.mapIso (V.mapIso contact))
  let e₂ := Q.mapIso ((E.inverse.mapIso (eqToIso hDecoded).symm) ≪≫ E.unitIso.symm.app w)
  let e₃ := eqToIso hContract
  let e₄ := I.mapIso (leftM.prod leftN)
  let e₅ := eqToIso hz.symm
  exact e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅


set_option maxHeartbeats 180000 in
private theorem retained_nativeCoordinates (z : Tensor (row M a) (column N d)) :
    z = nativeRetained M N (a := a) (k := z.as.mid) (d := d) z.as.first z.as.second := by
  rcases z with ⟨⟨i, x, y⟩⟩
  rfl

set_option maxHeartbeats 220000 in
/-- The objectwise left-unit comparison covers every retained object. -/
@[no_expose]
noncomputable def mixedLeftIdentityOnObjects
    (contact : ∀ (i : B) (p : (row M a).obj ⟨i⟩),
      ((s.app ⟨i⟩).app ⟨op a⟩).toFunctor.obj (innerBefore M N jN p) ≅ innerAfter M N jN p)
    (leftM : ∀ (i : B) (p : (row M a).obj ⟨i⟩),
      ((m.app ⟨i⟩).app ⟨op a⟩).toFunctor.obj (rowInputM M jM p) ≅ p)
    (leftN : ∀ (i : B) (q : (column N d).obj ⟨op i⟩),
      ((n.app ⟨d⟩).app ⟨op i⟩).toFunctor.obj (rowInputN N jN q) ≅ q)
    (z : Tensor (row M a) (column N d)) :
    (mixedLeftIdentityComposite.{v,u} M N jM jN s m n a d).obj z ≅ z := by
  let i : B := z.as.mid
  let p : (row M a).obj ⟨i⟩ := z.as.first
  let q : (column N d).obj ⟨op i⟩ := z.as.second
  have hz := retained_nativeCoordinates M N (a := a) (d := d) z
  have hc := contact i p
  have hm := leftM i p
  have hn := leftN i q
  exact mixedLeftIdentityAt.{v,u} M N jM jN s m n (a := a) (k := i) (d := d)
    p q z hz hc hm hn

end ContextualComposition.RelativeTensor.Iterated
