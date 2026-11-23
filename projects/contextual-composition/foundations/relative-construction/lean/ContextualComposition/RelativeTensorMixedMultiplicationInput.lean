module
public import ContextualComposition.RelativeTensorExposedCrossingInput
public import ContextualComposition.RelativeTensorContractionInput

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

/-- The two vertical equivalences may have nontrivial units and counits. Only
their inverses, never the supplied crossing, are used in reversing a square. -/
def reverseInputSquare {A B A' B' : Type*} [Category* A] [Category* B]
    [Category* A'] [Category* B'] (e : A ≌ B) (e' : A' ≌ B')
    {u : A ⥤ A'} {v : B ⥤ B'} (h : u ⋙ e'.functor ≅ e.functor ⋙ v) :
    v ⋙ e'.inverse ≅ e.inverse ⋙ u :=
  Iso.compInverseIso (H := e') (G := e.inverse ⋙ u) (Iso.isoInverseComp (G := e) h.symm)

/-- Paste adjacent input-change isomorphisms by functor whiskering. -/
def pasteInputSquare {A B C A' B' C' : Type*} [Category* A] [Category* B]
    [Category* C] [Category* A'] [Category* B'] [Category* C']
    {u : A ⥤ A'} {v : B ⥤ B'} {w : C ⥤ C'} {f : A ⥤ B} {f' : A' ⥤ B'}
    {g : B ⥤ C} {g' : B' ⥤ C'} (h : u ⋙ f' ≅ f ⋙ v) (k : v ⋙ g' ≅ g ⋙ w) :
    u ⋙ (f' ⋙ g') ≅ (f ⋙ g) ⋙ w :=
  Functor.isoWhiskerRight h g' ≪≫ Functor.isoWhiskerLeft f k

universe v u vM uM vN uN vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable {X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (t : X ⟶ X')
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

private theorem firstPortHom {P Q : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} (p : P ⟶ Q)
    (R : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
    {a b : LocallyDiscrete B} (f : a ⟶ b) (z : Tensor P (R.obj a)) :
    ((firstMap p R).naturality f).hom.toNatTrans.app z = 𝟙 _ := by
  change (eqToHom (factor_order p (R.map f)).symm).app z = _
  rw [eqToHom_app]; rfl

/-- Column component of naturality of the first pentagon edge in the first factor. -/
def outerInputAt (d : LocallyDiscrete B) :
    (firstMap (firstMap t M) N ≫ outerAssociator X' M N).app d ≅
      (outerAssociator X M N ≫ firstMap t (middleComposite M N)).app d :=
  Cat.Hom.isoMk (eqToIso (first_naturality t M (N.obj d)))

private theorem outerInputAt_hom (d : LocallyDiscrete B) (z : (leftBrackets X M N).obj d) :
    (outerInputAt t M N d).hom.toNatTrans.app z = 𝟙 _ := by
  change (eqToHom (first_naturality t M (N.obj d))).app z = _
  rw [eqToHom_app]; rfl

/-- Naturality of the first pentagon edge before taking the outer tensor:
the full column functors agree by first-factor naturality of reassociation. -/
def outerAssociatorInput :
    firstMap (firstMap t M) N ≫ outerAssociator X' M N ≅
      outerAssociator X M N ≫ firstMap t (middleComposite M N) :=
  Pseudofunctor.StrongTrans.isoMk (outerInputAt t M N) (by
    intro a b f
    apply Cat.Hom₂.ext; apply NatTrans.ext; funext z
    change (outerInputAt t M N b).hom.toNatTrans.app _ ≫
      𝟙 _ ≫ (mapFirst t).map ((fourthIndexSquare X M N f).hom.toNatTrans.app z) ≫ 𝟙 _ ≫
        ((firstMap t (middleComposite M N)).naturality f).hom.toNatTrans.app _ ≫ 𝟙 _ =
      (𝟙 _ ≫ (componentAt X' M N b).map (((firstMap (firstMap t M) N).naturality f).hom.toNatTrans.app z) ≫ 𝟙 _ ≫
        (fourthIndexSquare X' M N f).hom.toNatTrans.app _ ≫ 𝟙 _) ≫
        ((middleBrackets X' M N).map f).toFunctor.map ((outerInputAt t M N a).hom.toNatTrans.app z)
    simp only [outerInputAt_hom, fourthIndexSquare_app, firstPortHom, Functor.map_id, Category.id_comp, Category.comp_id]
    erw [Functor.map_id]
    rfl)

/-- At each column object the first-edge modification is identity; its
naturality still asserts a comparison of the complete localized functors. -/
theorem outerAssociatorInput_app (d : LocallyDiscrete B) (z : (leftBrackets X M N).obj d) :
    ((outerAssociatorInput t M N).hom.as.app d).toNatTrans.app z = 𝟙 _ :=
  outerInputAt_hom t M N d z

/-- Apply the outer tensor to the first-edge modification. -/
noncomputable def firstPentagonInput :
    mapFirst (G := Y) (firstMap (firstMap t M) N) ⋙ (firstPentagonEquivalence X' M N Y).functor ≅
      (firstPentagonEquivalence X M N Y).functor ⋙ mapFirst (G := Y) (firstMap t (middleComposite M N)) :=
  eqToIso (First.map_composite (G := Y) (firstMap (firstMap t M) N) (outerAssociator X' M N)).symm ≪≫
  (First.homAction _ _ Y).mapIso (outerAssociatorInput t M N) ≪≫
  eqToIso (First.map_composite (outerAssociator X M N) (firstMap t (middleComposite M N)))

/-- The equivalence exposing the middle pair reindexes in the first payload. -/
noncomputable def exposeMiddleInput :
    mapFirst (G := rightInner N Y) (firstMap t M) ⋙ (exposeMiddle X' M N Y).functor ≅
      (exposeMiddle X M N Y).functor ⋙ mapFirst (G := Y) (firstMap t (middleComposite M N)) :=
  pasteInputSquare (reverseInputSquare (associator (leftInner X M) N Y)
    (associator (leftInner X' M) N Y) (eqToIso (first_naturality (firstMap t M) N Y)))
    (firstPentagonInput t M N Y)

/-- Reindex the original crossing between the opposed-pairs presentations,
including the forward and inverse changes of brackets. -/
noncomputable def crossMiddleInput (s : middleComposite N M ⟶ middleComposite M N) :
    mapFirst (G := rightInner M Y) (firstMap t N) ⋙ crossMiddle X' M N Y s ≅
      crossMiddle X M N Y s ⋙ mapFirst (G := rightInner N Y) (firstMap t M) :=
  pasteInputSquare (exposeMiddleInput t N M Y) (pasteInputSquare (eqToIso (exposedCrossing_input t M N Y s))
    (reverseInputSquare (exposeMiddle X M N Y) (exposeMiddle X' M N Y) (exposeMiddleInput t M N Y)))

section Multiplication
variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- Input-endpoint change for the actual mixed multiplication on H⊙H → H,
H = M⊙N. No invertibility of the crossing or native arrows is assumed. -/
noncomputable def mixedMultiplicationInput (s : middleComposite N M ⟶ middleComposite M N)
    (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) {a b : B} (f : a ⟶ b) (c : B) :
    backward (column (middleComposite (middleComposite M N) (middleComposite M N)) c) f ⋙
      mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n a c ≅
    mixedMultiplicationAt.{v,u,vM,uM,vN,uN} M N s m n b c ⋙ backward (column (middleComposite M N) c) f :=
  pasteInputSquare (eqToIso (rightRow_change M N f.op.toLoc (column (middleComposite M N) c)))
    (pasteInputSquare (crossMiddleInput (Middle.change M f.op.toLoc) M N (column N c) s)
      (mixedContractionInput.{v,u,vM,uM,vN,uN} M N m n f c))

end Multiplication
end ContextualComposition.RelativeTensor.Iterated
