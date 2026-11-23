module
public import ContextualComposition.RelativeTensorPresented

@[expose] public section
namespace ContextualComposition.RelativeTensor.Presented
open CategoryTheory Opposite Factorization
open scoped CategoryTheory.Bicategory
universe vK vL vC vD uK uL uC uD
variable {K : Type uK} {L : Type uL} {C : Type uC} {D : Type uD}
variable [Category.{vK} K] [Category.{vL} L] [Category.{vC} C] [Category.{vD} D]
variable (e : K ⥤ C) (d : L ⥤ C)
set_option backward.isDefEq.respectTransparency false

def paired (s : Object e d) : Source.Fibre e d s.middle := (CostructuredArrow.mk s.first, StructuredArrow.mk s.second)

def nativeMap (S : Cocone (input e) (output d) D) {s t : Object e d} (f : Source.ProductHom e d s t) :
    (S.fiber s.middle).obj (paired e d s) ⟶ (S.fiber t.middle).obj (paired e d t) := by
  obtain ⟨i,p,q,x,y⟩ := s
  obtain ⟨j,p',q',x',y'⟩ := t
  obtain ⟨a,b,h,sq,tq⟩ := f
  change i = j at h
  subst j
  exact (S.fiber i).map (productMap
    (CostructuredArrow.homMk (f := CostructuredArrow.mk x) (f' := CostructuredArrow.mk x') a (by simpa using sq))
    (StructuredArrow.homMk (f := StructuredArrow.mk y) (f' := StructuredArrow.mk y') b (by simpa using tq.symm)))

theorem native_fibre (S : Cocone (input e) (output d) D) {i : C} {x y : Source.Fibre e d i} (f : x ⟶ y) :
    nativeMap e d S (Source.fibreProduct e d f) = (S.fiber i).map f := by
  apply congrArg (S.fiber i).map
  apply Prod.ext
  · apply CostructuredArrow.hom_ext; rfl
  · apply StructuredArrow.hom_ext; rfl

theorem native_comp (S : Cocone (input e) (output d) D) {s t r : Object e d} (f : Source.ProductHom e d s t) (g : Source.ProductHom e d t r) :
    nativeMap e d S (Source.productComp e d f g) = nativeMap e d S f ≫ nativeMap e d S g := by
  obtain ⟨i,p,q,x,y⟩ := s
  obtain ⟨j,p',q',x',y'⟩ := t
  obtain ⟨k,p'',q'',x'',y''⟩ := r
  obtain ⟨a,b,h,sq,tq⟩ := f
  obtain ⟨a',b',h',sq',tq'⟩ := g
  change i = j at h
  change j = k at h'
  subst j; subst k
  change (S.fiber i).map _ = (S.fiber i).map _ ≫ (S.fiber i).map _
  rw [← (S.fiber i).map_comp]
  apply congrArg (S.fiber i).map
  apply Prod.ext
  · apply CostructuredArrow.hom_ext; rfl
  · apply StructuredArrow.hom_ext; rfl

def write (S : Cocone (input e) (output d) D) : Source.Cocone e d (D := D) where
  obj s := (S.fiber s.middle).obj (paired e d s)
  map := nativeMap e d S
  map_id s := by cases s; exact (S.fiber _).map_id _
  map_comp f g := native_comp e d S f g
  bal x u y := S.bal u (CostructuredArrow.mk x) (StructuredArrow.mk y)
  bal_id x y := by
    rw [S.unit]
    apply congrArg (S.fiber _).map
    apply Prod.ext
    · apply CostructuredArrow.hom_ext
      exact input_unit e _
    · apply StructuredArrow.hom_ext
      exact output_unit d _
  bal_comp x u v y := by
    rw [S.comp]
    congr 1
    · apply congrArg (S.fiber _).map
      apply Prod.ext
      · apply CostructuredArrow.hom_ext; rfl
      · apply StructuredArrow.hom_ext; exact output_comp d u v _
    · congr 1
      congr 1
      apply congrArg (S.fiber _).map
      apply Prod.ext
      · apply CostructuredArrow.hom_ext; exact input_comp e u v _
      · apply StructuredArrow.hom_ext; rfl
  bal_natural x x' u y y' α β hx hy :=
    S.natural u (CostructuredArrow.homMk (f := CostructuredArrow.mk x) (f' := CostructuredArrow.mk x') α hx)
      (StructuredArrow.homMk (f := StructuredArrow.mk y) (f' := StructuredArrow.mk y') β hy)

def writeCell {S T : Cocone (input e) (output d) D} (m : S ⟶ T) : write e d S ⟶ write e d T where
  app s := (m.components s.middle).app (paired e d s)
  native_naturality := by
    intro s t f
    obtain ⟨i,p,q,x,y⟩ := s
    obtain ⟨j,p',q',x',y'⟩ := t
    obtain ⟨a,b,h,sq,tq⟩ := f
    change i = j at h
    subst j
    exact (m.components i).naturality _
  balance_naturality x u y := m.square u (CostructuredArrow.mk x) (StructuredArrow.mk y)

def writeFunctor : Cocone (input e) (output d) D ⥤ Source.Cocone e d (D := D) where
  obj := write e d
  map := writeCell e d
  map_id _ := rfl
  map_comp _ _ := rfl

end ContextualComposition.RelativeTensor.Presented
