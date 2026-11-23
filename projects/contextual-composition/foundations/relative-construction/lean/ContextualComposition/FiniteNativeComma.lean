module
public import ContextualComposition.FinitePresentationCell
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-! Equation (1) of the reduction report at fixed endpoints. The display and quotient legs live in the slice and coslice of types, so the ambient hom is the literal comma hom used by retained-cell normalization. -/

@[expose] public section
namespace ContextualComposition.FiniteNativeComma
open CategoryTheory FiniteNormalization

universe u
variable {A B Y Z : Type u} (P : Presentation A B Y) (Q : Presentation A B Z)

def pack : Comma (Over.forget A) (Under.forget B) :=
  ⟨Over.mk (TypeCat.ofHom (Subtype.val : {a // P.domain a} → A)),
    Under.mk (TypeCat.ofHom P.block), TypeCat.ofHom P.selected⟩

def toComma (f : P.Cell Q id id) : pack P ⟶ pack Q where
  left := Over.homMk (TypeCat.ofHom fun d => ⟨d.val, f.domainMap d.val d.property⟩) rfl
  right := Under.homMk (TypeCat.ofHom f.labelMap) (by ext b; exact f.block_comm b)
  w := by ext d; exact (f.selected_comm d).symm

theorem over_value (g : pack P ⟶ pack Q) (d : {a // P.domain a}) :
    (g.left.left d).val = d.val := by
  exact congrArg (fun (k : {a // P.domain a} ⟶ A) => k d) (Over.w g.left)

def fromComma (g : pack P ⟶ pack Q) : P.Cell Q id id where
  domainMap a h := (congrArg Q.domain (over_value P Q g ⟨a,h⟩)).mp (g.left.left ⟨a,h⟩).property
  labelMap := g.right.right
  block_comm b := congrArg (fun (k : B ⟶ Z) => k b) (Under.w g.right)
  selected_comm d := by
    have w : Q.selected (g.left.left d) = g.right.right (P.selected d) :=
      congrArg (fun (k : {a // P.domain a} ⟶ Z) => k d) g.w
    exact w.symm.trans (congrArg Q.selected (Subtype.ext (over_value P Q g d)))

/-- Both directions preserve actual grade maps at these objects of the ambient comma category. -/
def nativeCellEquiv : P.Cell Q id id ≃ (pack P ⟶ pack Q) where
  toFun := toComma P Q
  invFun := fromComma P Q
  left_inv _ := Subsingleton.elim _ _
  right_inv g := by
    apply Comma.hom_ext
    · apply Over.OverMorphism.ext
      apply ConcreteCategory.hom_ext
      intro d
      exact Subtype.ext (over_value P Q g d).symm
    · apply Under.UnderMorphism.ext
      rfl

end ContextualComposition.FiniteNativeComma
