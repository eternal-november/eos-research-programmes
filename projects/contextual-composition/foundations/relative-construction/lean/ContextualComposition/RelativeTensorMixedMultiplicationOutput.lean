module
public import ContextualComposition.RelativeTensorMixedMultiplicationInput

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable {Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (t : Y ⟶ Y')

/-- The second-factor map on the actual column of a composite is the last-factor lift. -/
theorem middleComposite_map_eq_lastMap {a b : B} (f : a ⟶ b) :
    (middleComposite M N).map f.toLoc = lastMap M (N.map f.toLoc) := rfl

/-- Whole-row identification commutes with changing the second tensor factor. -/
theorem identifyFirst_last {F F' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (h : F = F') :
    mapSecond (F := F) t ⋙ (identifyFirst h Y').functor =
      (identifyFirst h Y).functor ⋙ mapSecond (F := F') t := by
  subst F'
  exact (Functor.comp_id (mapSecond (F := F) t)).trans (Functor.id_comp _).symm

/-- The equivalence exposing the middle pair reindexes in the last payload.
The inverse associator uses its actual unit and counit. -/
noncomputable def exposeMiddleOutput :
    mapSecond (F := leftInner X M) (lastMap N t) ⋙ (exposeMiddle X M N Y').functor ≅
      (exposeMiddle X M N Y).functor ⋙ mapSecond (F := leftInner X (middleComposite M N)) t :=
  pasteInputSquare
    (reverseInputSquare (associator (leftInner X M) N Y) (associator (leftInner X M) N Y')
      (eqToIso (last_naturality (leftInner X M) N t)))
    (eqToIso (factor_order (outerAssociator X M N) t).symm)

/-- Last-factor change commutes with the supplied crossing on the whole
opposed-pairs carrier, with both changes of brackets included. -/
noncomputable def crossMiddleOutput (s : middleComposite N M ⟶ middleComposite M N) :
    mapSecond (F := leftInner X N) (lastMap M t) ⋙ crossMiddle X M N Y' s ≅
      crossMiddle X M N Y s ⋙ mapSecond (F := leftInner X M) (lastMap N t) :=
  pasteInputSquare (exposeMiddleOutput X N M t)
    (pasteInputSquare (eqToIso (factor_order (liftCrossing X M N s) t).symm)
      (reverseInputSquare (exposeMiddle X M N Y) (exposeMiddle X M N Y') (exposeMiddleOutput X M N t)))

section Contraction

/-- Lift the modification of the second contraction through the whole tensor,
using factor interchange to keep the first contraction fixed. -/
def contractChangeLast {F X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G G' Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (r : F ⟶ X)
    (t : G ⟶ G') (t' : Y ⟶ Y') (n : G ⟶ Y) (n' : G' ⟶ Y') (e : t ≫ n' ≅ n ≫ t') :
    mapSecond (F := F) t ⋙ mapBoth r n' ≅ mapBoth r n ⋙ mapSecond (F := X) t' := by
  let h : mapSecond (F := X) t ⋙ mapSecond (F := X) n' ≅
      mapSecond (F := X) n ⋙ mapSecond (F := X) t' :=
    eqToIso (Second.map_composite (F := X) t n').symm ≪≫
      (Second.homAction X G Y').mapIso e ≪≫ eqToIso (Second.map_composite (F := X) n t')
  exact eqToIso (congrArg (· ⋙ mapSecond (F := X) n') (factor_order r t).symm) ≪≫
    Functor.isoWhiskerLeft (mapFirst (G := G) r) h

/-- The output contraction square retains the original modification cell in the
second component of the native pair, holding the contracted first component fixed. -/
theorem contractChangeLast_app {F X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}}
    {G G' Y Y' : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}} (r : F ⟶ X)
    (t : G ⟶ G') (t' : Y ⟶ Y') (n : G ⟶ Y) (n' : G' ⟶ Y')
    (e : t ≫ n' ≅ n ≫ t') (z : Tensor F G) :
    (contractChangeLast r t t' n n' e).hom.app z =
      (insertion X Y' z.as.mid).map
        (productMap (𝟙 ((First.part r z.as.mid).obj z.as.first))
          ((e.hom.as.app ⟨op z.as.mid⟩).toNatTrans.app z.as.second)) := by
  unfold contractChangeLast
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.mapIso_hom]
  change (eqToHom (congrArg (· ⋙ mapSecond (F := X) n') (factor_order r t).symm)).app z ≫
    (eqToHom (Second.map_composite (F := X) t n').symm).app ((mapFirst r).obj z) ≫
    (Second.mapCell (F := X) e.hom.as).app ((mapFirst r).obj z) ≫
    (eqToHom (Second.map_composite (F := X) n t')).app ((mapFirst r).obj z) = _
  rw [eqToHom_app, eqToHom_app, eqToHom_app]
  change 𝟙 _ ≫ (𝟙 _ ≫ (Second.mapCell (F := X) e.hom.as).app _ ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

end Contraction

section Multiplication
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- The contraction stage reindexes along the output using the actual strong
naturality isomorphism of the supplied N multiplication. -/
def mixedContractionOutput (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N)
    (a : B) {b c : B} (f : b ⟶ c) :
    mapSecond (F := leftInner (row M a) M) (lastMap N (N.map f.toLoc)) ⋙
      mapBoth (rowMultiplication.{v,u,vM,uM} M m a) (n.app ⟨c⟩) ≅
    mapBoth (rowMultiplication.{v,u,vM,uM} M m a) (n.app ⟨b⟩) ⋙
      mapSecond (F := row M a) (N.map f.toLoc) :=
  contractChangeLast (rowMultiplication.{v,u,vM,uM} M m a) ((middleComposite N N).map f.toLoc)
    (N.map f.toLoc) (n.app ⟨b⟩) (n.app ⟨c⟩) (n.naturality f.toLoc)

/-- Output-endpoint change for the original mixed multiplication on H⊙H → H,
H = M⊙N, with the input endpoint fixed. The crossing need not be invertible. -/
noncomputable def mixedMultiplicationOutput (s : middleComposite N M ⟶ middleComposite M N)
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) (a : B) {b c : B} (f : b ⟶ c) :
    (((middleComposite (middleComposite M N) (middleComposite M N)).map f.toLoc).app ⟨op a⟩).toFunctor ⋙
      mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a c ≅
    mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a b ⋙
      (((middleComposite M N).map f.toLoc).app ⟨op a⟩).toFunctor :=
  pasteInputSquare (eqToIso (identifyFirst_last ((middleComposite M N).map f.toLoc) (middleRow M N a)))
    (pasteInputSquare (crossMiddleOutput (row M a) M N (N.map f.toLoc) s)
      (mixedContractionOutput.{v,u,vM,uM,vN,uN} M N m n a f))

end Multiplication
end ContextualComposition.RelativeTensor.Iterated
