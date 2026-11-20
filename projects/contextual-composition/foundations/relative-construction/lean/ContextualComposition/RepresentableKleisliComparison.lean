module
public import ContextualComposition.RepresentableKleisliCoherent
public import ContextualComposition.RepresentableComparisonPseudofunctor
public import ContextualComposition.RepresentableComparisonBinaryPin
public import ContextualComposition.RepresentableCommaComposition
@[expose] public section
namespace ContextualComposition.GrothendieckStep.RepresentableKleisliComparison
open CategoryTheory CategoryTheory.Bicategory
open AmbientCoherentPseudomonad RepresentableKleisli RepresentableKleisliBicategory
open RepresentableKleisliCoherent
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} B} {S : P.Split} (T : Data S)
abbrev N (P : Endpoints.{u,u,u,u} B) (x y : Part B) := CostructuredArrow (P.extend x.as) y.as
def e (x y : Part B) : N P x y ≌ KH S x.as y.as :=
  (commaEquiv (S := S) (A := x.as) (D := y.as)).symm
noncomputable def data :
    @RepresentableComparisonTransport.Data (Part B) (bicategory T) (N P) (fun _ _ => inferInstance) :=
  @RepresentableComparisonEquivalences.data (Part B) (bicategory T) (N P) (fun _ _ => inferInstance) (e (S := S))
noncomputable abbrev Native := @RepresentableComparisonPseudofunctor.Source (Part B) (bicategory T) (N P) _ (data T)
@[instance_reducible]
noncomputable def nativeBicategory : Bicategory (Native T) :=
  @RepresentableComparisonPseudofunctor.sourceBicategory (Part B) (bicategory T) (N P) _ (data T)
noncomputable def embed : @Pseudofunctor (Native T) (nativeBicategory T) (Part B) (bicategory T) :=
  @RepresentableComparisonPseudofunctor.pseudo (Part B) (bicategory T) (N P) _ (data T)
theorem covers :
    letI : Bicategory (Part B) := bicategory T
    letI : Bicategory (Native T) := nativeBicategory T
    Function.Surjective (embed T).obj :=
  @RepresentableComparisonPseudofunctor.onto (Part B) (bicategory T) (N P) _ (data T)
def asPart (x : Native T) : Part B :=
  @RepresentableComparisonPseudofunctor.Source.as (Part B) (bicategory T) (N P) _ (data T) x
def localEquivalence (x y : Native T) : N P (asPart T x) (asPart T y) ≌ KH S (asPart T x).as (asPart T y).as :=
  e (S := S) (asPart T x) (asPart T y)
theorem localMap (x y : Native T) :
    letI : Bicategory (Part B) := bicategory T
    letI : Bicategory (Native T) := nativeBicategory T
    (embed T).mapFunctor x y = (localEquivalence T x y).functor := rfl
theorem binaryExact (x y z : Part B) :
    @RepresentableComparisonEquivalences.binary (Part B) (bicategory T) x y z =
    (composeFunctor T (A := x.as) (D := y.as) (E := z.as)) :=
  RepresentableComparisonBinaryPin.binary (ops T) (laws T (actualLast T) (actualPent T)) x y z
theorem nativeComposition (x y z : Part B) :
    @RepresentableComparisonTransport.Data.mult (Part B) (bicategory T) (N P) _ (data T) x y z =
      RepresentableCommaComposition.comp T (A := x.as) (D := y.as) (E := z.as) := by
  change ((e (S := S) x y).functor.prod (e (S := S) y z).functor) ⋙
      (@RepresentableComparisonEquivalences.binary (Part B) (bicategory T) x y z) ⋙ (e (S := S) x z).inverse = _
  rw [binaryExact T x y z]
  rfl
theorem nativeUnit (x : Part B) :
    @RepresentableComparisonTransport.Data.unit (Part B) (bicategory T) (N P) _ (data T) x =
      CostructuredArrow.mk (Y := T.unit.grade x.as) (T.unit.discharge x.as) := by
  change (RepresentableComma.read (P.extend x.as) x.as).obj (row (unit T x.as)) = _
  rw [identityAt T x.as]
  rfl
end ContextualComposition.GrothendieckStep.RepresentableKleisliComparison
