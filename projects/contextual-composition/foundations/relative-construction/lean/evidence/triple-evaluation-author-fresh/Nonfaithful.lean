import ContextualComposition.TripleCuts
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep SpanApex NativeBlocks NativeBlocks.Nested TripleBoundary
namespace LossyBoundary
set_option backward.isDefEq.respectTransparency false
inductive B | star
instance : Subsingleton B := ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩
instance : Category B where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
inductive G | star
instance : Category G where
  Hom _ _ := List Nat
  id _ := []
  comp f g := f ++ g
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc ..
abbrev U : Span (B := B) := ⟨Cat.of B,𝟭 B,𝟭 B⟩
abbrev Y : Bᵒᵖ ⥤ Cat.{0,0} := (Functor.const _).obj (Cat.of G)
def x : Total Y U.dest := pair Y _ B.star G.star
def endo (w : List Nat) : x ⟶ x := arrow (𝟙 _) w
def forget : Total Y U.dest ⥤ Total Y (𝟭 B) := (Functor.const _).obj x
theorem over : forget ⋙ gradeProjection = gradeProjection ⋙ U.source := by
  fapply Functor.ext
  · intro _; apply Subsingleton.elim
  · intro x y f; exact @Subsingleton.elim Unit inferInstance _ _
example : ¬ forget.Faithful := by
  intro h
  have p : endo [1] = endo [2] := forget.map_injective (by rfl)
  exact (by decide : [1] ≠ [2]) (congrArg (fun g : x ⟶ x => payloadMap g) p)
example : lastPair U U U Y Y forget over ⋙ mid U U Y Y (𝟭 _) rfl =
  NativePacked.Lift.total (regroup U U U) Y ⋙ pairLast U U U Y Y Y forget over (𝟭 _) rfl :=
  associativity U U U Y Y Y forget over (𝟭 _) rfl
end LossyBoundary
