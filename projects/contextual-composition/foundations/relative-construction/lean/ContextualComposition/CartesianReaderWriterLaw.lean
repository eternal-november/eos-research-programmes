module

public import ContextualComposition.CartesianReader
public import ContextualComposition.CartesianWriter
public import ContextualComposition.MixedEffects

/-! The product swap for a fixed environment and an internal writer monoid,
as an instance of the four mixed distributive-law equations. -/

@[expose] public section
namespace ContextualComposition.CartesianReaderWriterLaw
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (E W : C) [MonObj W]

def environment : Comonad C where
  toFunctor := tensorLeft E
  ε := { app X := snd E X, naturality _ _ f := by simp }
  δ := { app X := lift (fst E X) (𝟙 _), naturality _ _ f := by simp }
  coassoc X := by simp
  left_counit X := by simp
  right_counit X := by simp

def writerJoin (X : C) : W ⊗ (W ⊗ X) ⟶ W ⊗ X :=
  lift (fst W _ * (snd W _ ≫ fst W X)) (snd W _ ≫ snd W X)

theorem writerJoin_eq (X : C) : writerJoin W X = CartesianWriter.join W X := by
  apply CartesianMonoidalCategory.hom_ext
  · change lift _ _ ≫ fst _ _ = (CartesianWriter.join W X) ≫ fst _ _
    simp [CartesianWriter.join]
    change lift _ _ ≫ μ[W] = _
    rw [← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · simp [writerJoin, CartesianWriter.join]

def writer : Monad C where
  toFunctor := tensorLeft W
  «η» := { app X := lift (1 : X ⟶ W) (𝟙 X), naturality _ _ f := by simp [MonObj.comp_one] }
  «μ» := { app X := writerJoin W X, naturality _ _ f := by simp [writerJoin, MonObj.comp_mul, Category.assoc] }
  assoc X := by simp [writerJoin, MonObj.comp_mul, _root_.mul_assoc, Category.assoc]
  left_unit X := by simp [writerJoin, MonObj.comp_mul]
  right_unit X := by simp [writerJoin, MonObj.comp_mul, MonObj.comp_one]

theorem coKleisli_comp {A B D : C} (f : E ⊗ A ⟶ B) (g : E ⊗ B ⟶ D) :
    ComonadRecovery.comp (environment E) f g = (CartesianReader.withEnvironment E).comp f g := by
  simp [ComonadRecovery.comp, environment, CartesianReader.withEnvironment]

theorem kleisli_comp {A B D : C} (f : A ⟶ W ⊗ B) (g : B ⟶ W ⊗ D) :
    MonadRecovery.comp (writer W) f g = CartesianWriter.writerComp W f g := by
  simp [MonadRecovery.comp, writer, CartesianWriter.writerComp, writerJoin_eq]

/-- The component maps (e,(w,x)) to (w,(e,x)). -/
def swap (X : C) : E ⊗ (W ⊗ X) ⟶ W ⊗ (E ⊗ X) :=
  lift (snd _ _ ≫ fst W X) (lift (fst _ _) (snd _ _ ≫ snd W X))

def law : MixedRecovery.Law (environment E) (writer W) where
  trans := { app X := swap E W X, naturality _ _ f := by simp [environment, writer, swap, Category.assoc] }
  unit X := by simp [environment, writer, swap, MonObj.comp_one]
  counit X := by simp [environment, writer, swap]
  mul X := by simp [environment, writer, swap, writerJoin, MonObj.comp_mul, Category.assoc]
  comul X := by simp [environment, writer, swap]

theorem law_component (X : C) : (law E W).trans.app X =
    lift (snd _ _ ≫ fst W X) (lift (fst _ _) (snd _ _ ≫ snd W X)) := rfl

end ContextualComposition.CartesianReaderWriterLaw
