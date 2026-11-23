module
public import ContextualComposition.NativeSpanProducts
public import ContextualComposition.NativeCommaReindex
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! Native products of span witnesses and their preservation by ordinary pullback at the input endpoint. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.NativeSpanBaseChange
open CategoryTheory CategoryTheory.Limits NativeSpanProducts NativeCommaProducts NativeCommaReindex
set_option backward.isDefEq.respectTransparency false
universe v u w
variable {C : Type u} [Category.{v} C] {A A' B : C} (a : A' ⟶ A) [HasPullbacksAlong a]

/-- The extension transformation of slice reindexing is the actual projection onto the old apex. -/
def extension : Over.pullback a ⋙ Over.forget A' ⟶ Over.forget A where
  app P := pullback.fst P.hom a
  naturality P Q c := by simp

theorem beckChevalley {P Q : Over A} (c : P ⟶ Q) :
    IsPullback ((Over.pullback a).map c).left ((extension a).app P) ((extension a).app Q) c.left := by
  let h := ((Over.pullback a).map c).left
  have fst : h ≫ pullback.fst Q.hom a = pullback.fst P.hom a ≫ c.left := by simp [h]
  have snd : h ≫ pullback.snd Q.hom a = pullback.snd P.hom a := by simp [h]
  apply IsPullback.of_right (h₁₂ := pullback.snd Q.hom a) (h₂₂ := Q.hom) (v₁₃ := a) _ fst
    (IsPullback.of_hasPullback Q.hom a).flip
  rw [snd,Over.w c]
  exact (IsPullback.of_hasPullback P.hom a).flip

variable {I : Type w} {D : I → Spans A B}

def gradePreservation (G : Grades D) : IsLimit (mappedContextFan (G:=G) (Over.pullback a)) :=
  Fan.isLimitMapConeEquiv _ _ _ (isLimitOfPreserves (Over.pullback a) G.ctxLim)

def preservesNative (G : Grades D) (U : Lift G) :
    IsLimit (Fan.mk ((input (Over.pullback a) (extension a)).obj (object U))
      (fun i => (input (Over.pullback a) (extension a)).map (projection U i))) :=
  mappedProduct _ _ U (gradePreservation a G) (domain_cartesian _) (beckChevalley a U.leg)

def point : One := ⟨⟨⟩⟩
def contentFan (D : I → Spans A B) : Fan (fun i => (D i).right) :=
  Fan.mk point (fun _ => eqToHom (Subsingleton.elim _ _))

def contentLimit (D : I → Spans A B) : IsLimit (contentFan D) :=
  Fan.IsLimit.mk _ (fun _ => eqToHom (Subsingleton.elim _ _)) (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ _ => Subsingleton.elim _ _)

def selectedGrades (D : I → Spans A B) [HasProduct (fun i => (D i).left)]
    [HasProduct (fun i => (content B).obj (D i).right)] : Grades D where
  ctx := limit.cone _
  ctxLim := limit.isLimit _
  con := contentFan D
  conLim := contentLimit D
  base := limit.cone _
  baseLim := limit.isLimit _

/-- Ordinary finite limits in the base suffice even when the constant content functor does not preserve products. -/
def finiteGrades [HasFiniteLimits C] {J : Type} [Finite J] (D : J → Spans A B) : Grades D :=
  selectedGrades D

/-- These are actual products in the native comma category, including the empty family. -/
theorem hasFiniteSpanProduct [HasFiniteLimits C] {J : Type} [Finite J] (D : J → Spans A B) : HasProduct D :=
  let U := spanProduct (finiteGrades D)
  ⟨⟨⟨productFan U,productLimit U⟩⟩⟩

end ContextualComposition.NativeSpanBaseChange
