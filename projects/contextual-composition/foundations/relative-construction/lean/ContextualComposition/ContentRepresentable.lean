module
public import ContextualComposition.ContentCoBicategory
public import ContextualComposition.ContentComma
public import ContextualComposition.RepresentableKleisliComparison
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContentRepresentable
open CategoryTheory CategoryTheory.Bicategory Opposite
open AmbientCoherentPseudomonad RepresentableKleisli RepresentableKleisliBicategory RepresentableKleisliCoherent
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1250000
universe u

section OneOpposite
variable {D : Type*} [Bicategory D]
/-- The 1-cell opposite exchanges the endpoints and preserves the direction
of every 2-cell. Both functors act on *all* 2-cells. -/
def oneOpLocal (a b : D) :
    (@Quiver.Hom D _ a b) ≌ (op b ⟶ op a) :=
  CategoryTheory.Equivalence.mk (Bicategory.Opposite.opFunctor a b) (Bicategory.Opposite.unopFunctor (op b) (op a))
    (Iso.refl _) (Iso.refl _)
end OneOpposite

variable {B : Type u} [Category.{u} B] {P : Endpoints.{u,u,u,u} Bᵒᵖ} {S : P.Split} (T : Data S)
abbrev Corep := Part Bᵒᵖ
abbrev PartOp := (Corep (B := B))ᵒᵖ
def corepAt (x : B) : Corep (B := B) := ⟨op x⟩
def contentAt (x : B) : PartOp (B := B) := op (corepAt x)

/-- Pointwise fibre opposite converts the dual-context chart into the
covariant chart. The semantic 1-cell reversal happens separately below. -/
@[instance_reducible]
noncomputable def corepresentable : Bicategory (Corep (B := B)) :=
  RepresentableBicategoryAssembly.build (ContentCoBicategory.ops (ops T))
    (ContentCoBicategory.laws (ops T) (laws T (actualLast T) (actualPent T)))

@[instance_reducible]
noncomputable def content : Bicategory (PartOp (B := B)) :=
  letI : Bicategory (Corep (B := B)) := corepresentable T
  Bicategory.Opposite.bicategory

abbrev N (x y : PartOp (B := B)) := ContentComma.Native P x.unop.as.unop y.unop.as.unop

noncomputable def localEquivalence (x y : PartOp (B := B)) :
    letI : Bicategory (PartOp (B := B)) := content T
    (x ⟶ y) ≌ N (P := P) x y := by
  letI : Bicategory (Corep (B := B)) := corepresentable T
  exact (oneOpLocal y.unop x.unop).symm.trans
    ((commaEquiv (S := S) (A := y.unop.as) (D := x.unop.as)).op.trans
      (ContentComma.iso P x.unop.as.unop y.unop.as.unop).toEquivalence)

noncomputable def data :
    @RepresentableComparisonTransport.Data (PartOp (B := B)) (content T) (N (P := P)) (fun _ _ => inferInstance) :=
  @RepresentableComparisonEquivalences.data (PartOp (B := B)) (content T) (N (P := P)) (fun _ _ => inferInstance)
    (fun x y => (localEquivalence T x y).symm)

noncomputable abbrev Native :=
  @RepresentableComparisonPseudofunctor.Source (PartOp (B := B)) (content T) (N (P := P)) _ (data T)

@[instance_reducible]
noncomputable def nativeBicategory : Bicategory (Native T) :=
  @RepresentableComparisonPseudofunctor.sourceBicategory (PartOp (B := B)) (content T) (N (P := P)) _ (data T)

noncomputable def embed : @Pseudofunctor (Native T) (nativeBicategory T) (PartOp (B := B)) (content T) :=
  @RepresentableComparisonPseudofunctor.pseudo (PartOp (B := B)) (content T) (N (P := P)) _ (data T)

def asContent (x : Native T) : PartOp (B := B) :=
  @RepresentableComparisonPseudofunctor.Source.as (PartOp (B := B)) (content T) (N (P := P)) _ (data T) x

theorem localMap (x y : Native T) :
    letI : Bicategory (PartOp (B := B)) := content T
    letI : Bicategory (Native T) := nativeBicategory T
    (embed T).mapFunctor x y = (localEquivalence T (asContent T x) (asContent T y)).inverse := rfl

theorem covers :
    letI : Bicategory (PartOp (B := B)) := content T
    letI : Bicategory (Native T) := nativeBicategory T
    Function.Surjective (embed T).obj :=
  @RepresentableComparisonPseudofunctor.onto (PartOp (B := B)) (content T) (N (P := P)) _ (data T)

end ContextualComposition.GrothendieckStep.ContentRepresentable
