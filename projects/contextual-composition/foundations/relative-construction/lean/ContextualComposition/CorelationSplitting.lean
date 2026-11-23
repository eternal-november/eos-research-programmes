module
public import Init

/-! Splitting source-only classes, the partition-level coreflection of equation (9) of the finite reduction report. -/

@[expose] public section
namespace ContextualComposition.CorelationSplitting

universe u v
variable {A : Type u} {B : Type v}

/-- The class of an endpoint contains a target point. -/
def MeetsTarget (P : Setoid (Sum A B)) (x : Sum A B) : Prop :=
  ∃ b : B, P.r x (.inr b)

/-- Every class containing two distinct points contains a target point. -/
def Normal (P : Setoid (Sum A B)) : Prop :=
  ∀ x y, P.r x y → x = y ∨ MeetsTarget P x

def Refines (P Q : Setoid (Sum A B)) : Prop := ∀ x y, P.r x y → Q.r x y

/-- Keep each target-meeting class and split the remaining classes into singletons. -/
def split (P : Setoid (Sum A B)) : Setoid (Sum A B) where
  r x y := x = y ∨ (P.r x y ∧ MeetsTarget P x)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with rfl | ⟨hxy, b, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨P.symm hxy, b, P.trans (P.symm hxy) hb⟩
    trans := by
      intro x y z h k
      rcases h with rfl | ⟨hxy, hit⟩
      · exact k
      rcases k with rfl | ⟨hyz, _⟩
      · exact Or.inr ⟨hxy, hit⟩
      · exact Or.inr ⟨P.trans hxy hyz, hit⟩ }

theorem split_normal (P : Setoid (Sum A B)) : Normal (split P) := by
  intro x y h
  rcases h with he | ⟨_, b, hb⟩
  · exact Or.inl he
  · exact Or.inr ⟨b, Or.inr ⟨hb, b, hb⟩⟩

theorem split_refines (P : Setoid (Sum A B)) : Refines (split P) P := by
  intro x y h
  rcases h with rfl | ⟨hxy, _⟩
  · exact P.refl _
  · exact hxy

/-- Inclusion of normalized partitions is left adjoint to splitting, in the refinement order. -/
theorem coreflection (P Q : Setoid (Sum A B)) (hP : Normal P) :
    Refines P Q ↔ Refines P (split Q) := by
  constructor
  · intro f x y h
    rcases hP x y h with he | ⟨b, hb⟩
    · exact Or.inl he
    · exact Or.inr ⟨f x y h, b, f x _ hb⟩
  · intro f x y h
    exact split_refines Q x y (f x y h)

theorem split_fixed (P : Setoid (Sum A B)) (hP : Normal P) : split P = P := by
  have eqr : (split P).r = P.r := by
    funext x y
    exact propext ⟨split_refines P x y, ((coreflection P P hP).mp (fun _ _ h => h)) x y⟩
  exact (show ∀ S T : Setoid (Sum A B), S.r = T.r → S = T by
    intro ⟨_, _⟩ ⟨_, _⟩ h; cases h; rfl) _ _ eqr

end ContextualComposition.CorelationSplitting
