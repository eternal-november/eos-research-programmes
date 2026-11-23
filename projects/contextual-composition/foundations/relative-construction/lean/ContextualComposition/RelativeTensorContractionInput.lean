module
public import ContextualComposition.RelativeTensorRowMultiplicationChange

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe v u vX uX vY uY vM uM vN uN
variable {B : Type u} [Category.{v} B]

/-- A modification of the first-factor contraction induces a square between the full tensor functors after contracting both factors. -/
def contractChange {F F' X X' : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}} {G Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY}}
    (t : F ⟶ F') (t' : X ⟶ X') (r : F ⟶ X) (r' : F' ⟶ X') (n : G ⟶ Y)
    (e : t ≫ r' ≅ r ≫ t') :
    mapFirst (G := G) t ⋙ mapBoth r' n ≅ mapBoth r n ⋙ mapFirst (G := Y) t' := by
  let h : mapFirst (G := G) t ⋙ mapFirst (G := G) r' ≅ mapFirst (G := G) r ⋙ mapFirst (G := G) t' :=
    eqToIso (First.map_composite (G := G) t r').symm ≪≫ (First.homAction F X' G).mapIso e ≪≫ eqToIso (First.map_composite (G := G) r t')
  exact Functor.isoWhiskerRight h (mapSecond (F := X') n) ≪≫ eqToIso (congrArg (mapFirst (G := G) r ⋙ ·) (factor_order t' n))

variable (M : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vM uM,max u uM}))
variable (N : LocallyDiscrete B ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{max u v vN uN,max u uN}))

/-- The entire MM/NN contraction stage of mixed multiplication reindexes along the input endpoint. -/
def mixedContractionInput (m : middleComposite M M ⟶ M) (n : middleComposite N N ⟶ N) {a b : B} (f : a ⟶ b) (c : B) :
    mapFirst (G := rightInner N (column N c)) (firstMap (Middle.change M f.op.toLoc) M) ⋙
      mapBoth (rowMultiplication.{v,u,vM,uM} M m a) (n.app ⟨c⟩) ≅
    mapBoth (rowMultiplication.{v,u,vM,uM} M m b) (n.app ⟨c⟩) ⋙ mapFirst (G := column N c) (Middle.change M f.op.toLoc) :=
  contractChange (firstMap (Middle.change M f.op.toLoc) M) (Middle.change M f.op.toLoc)
    (rowMultiplication.{v,u,vM,uM} M m b) (rowMultiplication.{v,u,vM,uM} M m a) (n.app ⟨c⟩)
    (rowMultiplication_change.{v,u,vM,uM} M m f)

end ContextualComposition.RelativeTensor.Iterated
