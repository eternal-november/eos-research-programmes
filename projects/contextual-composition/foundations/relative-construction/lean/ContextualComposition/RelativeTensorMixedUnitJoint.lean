module
public import ContextualComposition.RelativeTensorMixedUnitInputCoherence
public import ContextualComposition.RelativeTensorMixedEndpointCompatibility
@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
universe v u
variable {B : Type u} [Category.{v} B]
variable (M N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}))
variable (jM : unitModule B ⟶ M) (jN : unitModule B ⟶ N)
variable {a b c d : B} (f : a ⟶ b) (g : c ⟶ d)

/-- Exact joint compatibility of the original mixed unit comparisons with
both specified endpoint interchangers. -/
def MixedUnitJoint : Prop :=
  JointEndpointSquare (endpointInterchange (unitModule B) f g)
    (endpointInterchange (middleComposite M N) f g)
    (mixedUnitInput M N jM jN (b := c) f)
    (mixedUnitInput M N jM jN (b := d) f)
    (mixedUnitOutput M N jM jN (a := b) g)
    (mixedUnitOutput M N jM jN (a := a) g)

set_option maxHeartbeats 300000 in
private theorem targetSwap (x : Tensor (row M b) (column N c)) :
    (endpointInterchange (middleComposite M N) f g).hom.app x = 𝟙 _ :=
  Parametric.interchange_app (Middle.change M f.op.toLoc) (N.map g.toLoc) x

private abbrev inputCell (k : B) (p : Discrete (b ⟶ k)) :=
  ((jM.app ⟨k⟩).naturality f.op.toLoc).hom.toNatTrans.app p

set_option maxHeartbeats 500000 in
private theorem firstPayloadJoint (p : Discrete (b ⟶ c)) :
    (mixedUnitOutputFirst M jM g (f ≫ p.as)).hom ≫
        (forward (row M a) g).map (inputCell M jM f c p) =
      ((jM.app ⟨d⟩).app ⟨op a⟩).toFunctor.map
          ((endpointInterchange (unitModule B) f g).hom.app p) ≫
        inputCell M jM f d (Discrete.mk (p.as ≫ g)) ≫
        (First.part (Middle.change M f.op.toLoc) d).map
          (mixedUnitOutputFirst M jM g p.as).hom ≫
        (First.port (Middle.change M f.op.toLoc) g (nativeUnitValue jM p.as)).inv := by
  have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans
    ((jM.naturality g.toLoc).hom.as.naturality f.op.toLoc)) p
  let beta := (mixedUnitOutputFirst M jM g (f ≫ p.as)).hom
  let alpha := (forward (row M a) g).map (inputCell M jM f c p)
  let e := First.port (Middle.change M f.op.toLoc) g (nativeUnitValue jM p.as)
  let k := ((jM.app ⟨d⟩).app ⟨op a⟩).toFunctor.map
    ((endpointInterchange (unitModule B) f g).hom.app p)
  let l := inputCell M jM f d (Discrete.mk (p.as ≫ g))
  let t := (First.part (Middle.change M f.op.toLoc) d).map
    (mixedUnitOutputFirst M jM g p.as).hom
  change beta ≫ (𝟙 _ ≫ alpha ≫ 𝟙 _ ≫ e.hom ≫ 𝟙 _) =
    (𝟙 _ ≫ k ≫ 𝟙 _ ≫ l ≫ 𝟙 _) ≫ t at h
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at h
  change beta ≫ alpha = k ≫ l ≫ t ≫ e.inv
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h

private theorem nativePair_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C × D ⥤ E) {x y z : C} {x' y' z' : D}
    (u : x ⟶ y) (v : x' ⟶ y') (s : y ⟶ z) (t : y' ⟶ z') :
    J.map (productMap u v) ≫ J.map (productMap s t) = J.map (productMap (u ≫ s) (v ≫ t)) :=
  (J.map_comp _ _).symm

private theorem pairSwap {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C × D ⥤ E) {x y : C} {x' y' : D} (s : x ⟶ y) (t : x' ⟶ y') :
    J.map (productMap (𝟙 x) t) ≫ J.map (productMap s (𝟙 y')) =
      J.map (productMap s (𝟙 x')) ≫ J.map (productMap (𝟙 y) t) := by
  rw [nativePair_comp, nativePair_comp]
  simp only [Category.id_comp, Category.comp_id]

private theorem inverseBalance_naturality_first
    {F : LocallyDiscrete B ⥤ᵖ Cat.{v,v}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}}
    {x x' : F.obj ⟨c⟩} (s : x ⟶ x') (y : G.obj ⟨op d⟩) :
    (balancing F G g x y).inv ≫ (insertion F G c).map (productMap s (𝟙 ((backward G g).obj y))) =
      (insertion F G d).map (productMap ((forward F g).map s) (𝟙 y)) ≫
        (balancing F G g x' y).inv := by
  apply (cancel_epi (balancing F G g x y).hom).mp
  apply (cancel_mono (balancing F G g x' y).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change (quotient F G).map (nativePath F G s (𝟙 _)) ≫ (quotient F G).map (balancePath F G g x' y) =
    (quotient F G).map (balancePath F G g x y) ≫
      (quotient F G).map (nativePath F G ((forward F g).map s) (𝟙 y))
  rw [← (quotient F G).map_comp, ← (quotient F G).map_comp, ← (backward G g).map_id]
  exact CategoryTheory.Quotient.sound _ (Relations.natural g s (𝟙 y))

private theorem payloadPaste
    {F : LocallyDiscrete B ⥤ᵖ Cat.{v,v}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{v,v}}
    {x x' : F.obj ⟨c⟩} {z w₁ w₂ w₃ : F.obj ⟨d⟩}
    (y : G.obj ⟨op d⟩) {y' : G.obj ⟨op c⟩}
    (A : x ⟶ x') (S : (backward G g).obj y ⟶ y')
    (beta : z ⟶ (forward F g).obj x) (k : z ⟶ w₁) (l : w₁ ⟶ w₂)
    (T : w₂ ⟶ w₃) (e : w₃ ⟶ (forward F g).obj x')
    (h : beta ≫ (forward F g).map A = k ≫ l ≫ T ≫ e) :
    let J := insertion F G d
    let K := insertion F G c
    (J.map (productMap beta (𝟙 y)) ≫ (balancing F G g x y).inv ≫
      K.map (productMap (𝟙 x) S)) ≫ K.map (productMap A (𝟙 y')) =
    J.map (productMap k (𝟙 y)) ≫ J.map (productMap l (𝟙 y)) ≫
      J.map (productMap T (𝟙 y)) ≫
        (J.map (productMap e (𝟙 y)) ≫ (balancing F G g x' y).inv) ≫
        K.map (productMap (𝟙 x') S) := by
  dsimp only
  simp only [Category.assoc]
  rw [pairSwap (insertion F G c) A S, reassoc_of% inverseBalance_naturality_first g A y]
  simp only [← Category.assoc]
  simp only [nativePair_comp, Category.comp_id, Category.assoc, h]

set_option maxHeartbeats 800000 in
/-- The original mixed unit comparisons agree in both endpoint orders on the
retained quotient. -/
theorem mixedUnitInputOutput_compatibility : MixedUnitJoint M N jM jN f g := by
  unfold MixedUnitJoint
  intro x
  rw [targetSwap]
  erw [Category.comp_id]
  revert x
  change ∀ p : Discrete (b ⟶ c), _
  intro p
  change (mixedUnitOutput M N jM jN (a := a) g).hom.app (Discrete.mk (f ≫ p.as)) ≫
    (mapSecond (F := row M a) (N.map g.toLoc)).map
      ((mixedUnitInput M N jM jN (b := c) f).hom.app p) =
    (mixedUnitAt M N jM jN a d).map ((endpointInterchange (unitModule B) f g).hom.app p) ≫
    (mixedUnitInput M N jM jN (b := d) f).hom.app (Discrete.mk (p.as ≫ g)) ≫
    (mapFirst (G := column N d) (Middle.change M f.op.toLoc)).map
      ((mixedUnitOutput M N jM jN (a := b) g).hom.app p)
  erw [mixedUnitOutput_app, mixedUnitOutput_app, mixedUnitInput_app, mixedUnitInput_app,
    mixedUnitAt_map, Second.on_native, Functor.map_id, Functor.map_comp, Functor.map_comp,
    First.on_native, First.on_native, Functor.map_id, firstMap_inverseBalance]
  let J := insertion (row M a) (column N d) d
  let K := insertion (row M a) (column N d) c
  let y := nativeUnitValue jN (𝟙 d)
  let L := nativeUnitValue jM (f ≫ p.as)
  let R := (First.part (Middle.change M f.op.toLoc) c).obj (nativeUnitValue jM p.as)
  let A := inputCell M jM f c p
  let S := (mixedUnitOutputSecond N jN g).hom
  let beta := (mixedUnitOutputFirst M jM g (f ≫ p.as)).hom
  let k := ((jM.app ⟨d⟩).app ⟨op a⟩).toFunctor.map
    ((endpointInterchange (unitModule B) f g).hom.app p)
  let l := inputCell M jM f d (Discrete.mk (p.as ≫ g))
  let T := (First.part (Middle.change M f.op.toLoc) d).map
    (mixedUnitOutputFirst M jM g p.as).hom
  let e := (First.port (Middle.change M f.op.toLoc) g (nativeUnitValue jM p.as)).inv
  change (J.map (productMap beta (𝟙 y)) ≫ (balancing (row M a) (column N d) g L y).inv ≫
      K.map (productMap (𝟙 L) S)) ≫ K.map (productMap A (𝟙 _)) =
    J.map (productMap k (𝟙 y)) ≫ J.map (productMap l (𝟙 y)) ≫
      J.map (productMap T (𝟙 y)) ≫
        (J.map (productMap e (𝟙 y)) ≫ (balancing (row M a) (column N d) g R y).inv) ≫
        K.map (productMap (𝟙 R) S)
  exact payloadPaste g y A S beta k l T e (firstPayloadJoint M jM f g p)

end ContextualComposition.RelativeTensor.Iterated
