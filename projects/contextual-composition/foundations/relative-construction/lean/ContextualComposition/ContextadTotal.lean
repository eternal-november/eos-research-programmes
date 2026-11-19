module
public import ContextualComposition.ContextadCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.ContextadTotal
open CategoryTheory CategoryTheory.Functor Opposite NativeCleavage ContextadCartesian
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
universe b w u v
section Values
variable {B : Type*} [Category* B] (G H : Bᵒᵖ ⥤ Cat.{v,u})
variable (F : Total G (𝟭 B) ⥤ Total H (𝟭 B)) (over : F ⋙ FibreValue.proj H = FibreValue.proj G)
abbrev localValue (A : B) := FibreValue.embed G A ⋙ SpanPayload.fibreFunctor F (FibreValue.proj H) over A ⋙ FibreValue.value H A
variable (pres : ∀ {x y : Total G (𝟭 B)} (f : x ⟶ y),
  Cartesian (FibreValue.proj G) f → Cartesian (FibreValue.proj H) (F.map f))
noncomputable def valueSquare {A D : B} (a : D ⟶ A) :
    (G.map a.op).toFunctor ⋙ localValue G H F over D ≅ localValue G H F over A ⋙ (H.map a.op).toFunctor :=
  isoWhiskerRight (FibreValue.square G a) (SpanPayload.fibreFunctor F _ over D ⋙ FibreValue.value H D) ≪≫
    isoWhiskerLeft (FibreValue.embed G A)
      (isoWhiskerRight (Change.square F over (Route.ofChoice (FibreValue.choice G) a) (Route.ofChoice (FibreValue.choice H) a) pres) (FibreValue.value H D)) ≪≫
    isoWhiskerLeft (FibreValue.embed G A ⋙ SpanPayload.fibreFunctor F _ over A) (FibreValue.valueSquare H a)
end Values
open SpanApex NativeBlocks BlockEvaluation
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
/-- The cartesian right-colax map from the literal native sequential span to the one-stage span.
Its grade functor acts on all arrows above all bases, not only on the vertical fibres. -/
structure Native where
  grade : (power S 2).apex ⥤ (power S 1).apex
  over : grade ⋙ (power S 1).source = (power S 2).source
  delta : grade ⋙ (power S 1).dest ⟶ (power S 2).dest
  cart : ∀ {x y} (f : x ⟶ y), Cartesian (power S 2).source f → Cartesian (power S 1).source (grade.map f)
variable {S} (m : Native S) (Y : PackedCuts.Psh.{u,max u v,u,v} B)
abbrev action := weighted Y (power S 2).dest (power S 1).dest m.grade m.delta
theorem actionOver : action m Y ⋙ BlockEvaluation.proj S Y 1 = BlockEvaluation.proj S Y 2 :=
  weightedOver _ _ _ _ _ m.over
theorem actionCart {x y} (f : x ⟶ y) (hf : Cartesian (BlockEvaluation.proj S Y 2) f) :
    Cartesian (BlockEvaluation.proj S Y 1) ((action m Y).map f) :=
  weightedCartesian _ _ _ _ _ (powerChoice S 1) m.cart f hf
noncomputable abbrev total := (global S Y 2).strictInv ⋙ action m Y ⋙ global S Y 1
theorem totalOver : total m Y ⋙ FibreValue.proj (PackedFree.pow S Y 1) = FibreValue.proj (PackedFree.pow S Y 2) :=
  (congrArg ((global S Y 2).strictInv ⋙ action m Y ⋙ ·) (globalOver S Y 1)).trans
    ((congrArg ((global S Y 2).strictInv ⋙ ·) (actionOver m Y)).trans (BoundaryPaste.invOver _ _ _ (globalOver S Y 2)))
theorem totalCart {x y} (f : x ⟶ y) (hf : Cartesian (FibreValue.proj (PackedFree.pow S Y 2)) f) :
    Cartesian (FibreValue.proj (PackedFree.pow S Y 1)) ((total m Y).map f) := by
  apply (BlockCartesian.cartesian_iff (global S Y 1) (BlockCartesian.isoIncoming _) _ _).mp
  rw [globalOver]
  apply actionCart
  apply (BlockCartesian.cartesian_iff (global S Y 2).strictInv (BlockCartesian.isoIncoming _) _ _).mp
  rwa [BoundaryPaste.invOver _ _ _ (globalOver S Y 2)]
noncomputable abbrev binary (A : B) := localValue _ _ (total m Y) (totalOver m Y) A
noncomputable def exterior {A D : B} (a : D ⟶ A) :
    ((PackedFree.pow S Y 2).map a.op).toFunctor ⋙ binary m Y D ≅ binary m Y A ⋙ P.baseRestrict Y a :=
  valueSquare _ _ (total m Y) (totalOver m Y) (totalCart m Y) a
end ContextualComposition.GrothendieckStep.ContextadTotal
