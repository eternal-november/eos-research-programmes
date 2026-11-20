module
public import ContextualComposition.RepresentableBicategoryAssembly
public import ContextualComposition.RepresentableKleisliOriginal
public import ContextualComposition.RepresentableKleisliTriangle
public import ContextualComposition.RepresentableLeftUnitor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliBicategory
open CategoryTheory CategoryTheory.Bicategory
open RepresentableKleisli RepresentableKleisliConstraints AmbientCoherentPseudomonad
open RepresentableBicategoryAssembly
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
universe u
structure Part (B : Type u) where
  as : B
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
abbrev H (S : P.Split) (x y : Part B) := KH S x.as y.as
noncomputable abbrev ops : Operations (H S) where
  unit x := unit T x.as
  multiply := composeFunctor T
  left := leftUnit T
  right := rightUnit T
  assoc := reassociate T
variable {A D E J Q : B}
abbrev Last : Prop :=
  ∀ {A D E J : B} (f : KH S A D) (g : KH S D E) {h h' : KH S E J} (t : h ⟶ h'),
    composeCell T (𝟙 (compose T f g)) t ≫ (reassociate T f g h').hom =
    (reassociate T f g h).hom ≫ composeCell T (𝟙 f) (composeCell T (𝟙 g) t)
abbrev Pent : Prop :=
  ∀ {A D E J Q : B} (f : KH S A D) (g : KH S D E) (h : KH S E J) (i : KH S J Q),
    composeCell T (reassociate T f g h).hom (𝟙 i) ≫ (reassociate T f (compose T g h) i).hom ≫
        composeCell T (𝟙 f) (reassociate T g h i).hom =
     (reassociate T (compose T f g) h i).hom ≫ (reassociate T f g (compose T h i)).hom
theorem laws (L : Last T) (P₀ : Pent T) : Laws (ops T) := by
  constructor
  · intro x y f g t
    apply RepresentableLeftUnitor.original T t
  · intro x y f g t
    apply RepresentableRightUnitor.original T t
  · intro x y z r f f' t g h
    apply RepresentableAssociatorPrefix.original T t g h
  · intro x y z r f g g' t h
    apply RepresentableKleisliOriginal.middle T f t h
  · intro x y z r f g h h' t
    apply L f g t
  · intro x y z f g
    simpa only [RepresentableBicategoryAssembly.lW,RepresentableBicategoryAssembly.rW,
      RepresentableBicategoryAssembly.compCell,ops,composeFunctor] using
        RepresentableKleisliTriangle.original T (A := x.as) (D := y.as) (E := z.as) f g
  · intro x y z r s f g h i
    simpa only [RepresentableBicategoryAssembly.lW,RepresentableBicategoryAssembly.rW,
      RepresentableBicategoryAssembly.compCell,RepresentableBicategoryAssembly.cmp,ops,composeFunctor] using
        @P₀ x.as y.as z.as r.as s.as f g h i
@[instance_reducible]
noncomputable def assemble (L : Last T) (P₀ : Pent T) : Bicategory (Part B) :=
  RepresentableBicategoryAssembly.build (ops T) (laws T L P₀)
end ContextualComposition.GrothendieckStep.RepresentableKleisliBicategory
