module
public import ContextualComposition.AmbientCellFunctor
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientCellTrace
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload AmbientModificationAction AmbientBlockCells AmbientVerticalDescent AmbientRoundTrip AmbientCellFunctor
open WordTrace NativeBlocks ContextadWeakAction SpanApex BoundaryPaste
open scoped CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
section General
variable {C D : Type*} [Category* C] [Category* D]
def edge {x y : C} (f : x ⟶ y) : Edge C := ⟨_,_,f⟩
theorem same {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'} (h : Aligned f g) : edge f = edge g :=
  Edge.eq_of h.src h.dst (ContextadUnitTotal.alignedHEq h)
theorem edgePure {x y : C} {f : x ⟶ y} (p : Pure f) : edge f = edge (𝟙 x) := by
  obtain ⟨rfl,rfl⟩ := p; rfl
theorem reframe {F G F' G' : C ⥤ D} (l : F = F') (r : G' = G) (t : F' ⟶ G') (x) :
    edge ((eqToHom l ≫ t ≫ eqToHom r).app x) = edge (t.app x) := by subst F'; subst G'; simp
end General
section Decode
variable {B : Type u} [Category.{v} B] (Y Z : Bᵒᵖ ⥤ Cat.{v,u})
variable {F G : Total Y (𝟭 B) ⥤ Total Z (𝟭 B)} (h : F ⋙ proj Z = proj Y) (k : G ⋙ proj Z = proj Y)
variable (i : F ⟶ G) (v : ∀ x, Pure ((proj Z).map (i.app x))) (p : ContextadModification.Pres F (proj Y) (proj Z)) (q : ContextadModification.Pres G (proj Y) (proj Z))
theorem decoded (x : Total Y (𝟭 B)) : edge ((totalCell (descend Y Z h k i v p q)).app x) = edge (i.app x) := by
  rw [totalApp]
  let A := grade _ _ x
  let n := (fibre h k i v A).app ((embed Y A).obj (payload _ _ x))
  exact same (((NativeCube.functorAlign (value_embed Z A) n).map Fiber.fiberInclusion).trans (underlying h k i v A _))
variable {Y Z}
theorem cellExt {a b : StrongTrans Y.toPseudofunctor' Z.toPseudofunctor'} {t s : StrongTrans.Modification a b}
    (h : ∀ x, edge ((totalCell t).app x) = edge ((totalCell s).app x)) : t = s := by
  apply StrongTrans.Modification.ext; funext A
  apply Cat.Hom₂.ext; ext x : 2
  let I := incl Z A.as.unop
  let _ : I.Faithful := (inferInstance : (embed Z A.as.unop ⋙ Fiber.fiberInclusion).Faithful)
  apply I.map_injective
  specialize h ((incl Y A.as.unop).obj x)
  rw [totalApp,totalApp] at h
  exact eq_of_heq (Edge.hom_heq h)
end Decode
section Packed
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} (S : P.Split)
variable {U V : PackedCuts.Psh.{u,max u v,u,v} B} {a b : StrongTrans U.toPseudofunctor' V.toPseudofunctor'} (t : StrongTrans.Modification a b)
abbrev idEdge {C : Type*} [Category* C] (x : C) := edge (𝟙 x)
def grades (n : Nat) (x : Total (PackedFree.pow S U n) (𝟭 B)) := (WordTrace.read S U n (idEdge x)).1
def last (n : Nat) (x : Total (PackedFree.pow S U n) (𝟭 B)) := (WordTrace.read S U n (idEdge x)).2.src
theorem trace (n : Nat) (x : Total (PackedFree.pow S U n) (𝟭 B)) :
    WordTrace.read S V n (edge ((totalCell (blockMod S t n)).app x)) =
    (grades S n x,edge ((totalCell t).app (last S n x))) := by
  rw [show edge ((totalCell (blockMod S t n)).app x) = _ from decoded _ _ _ _ _ _ (blockPres S a n) (blockPres S b n) x]
  let G := BlockEvaluation.global S U n
  let w := G.strictInv.obj x
  let f := (endpointCell (power S n).dest t).app w
  change WordTrace.read S V n (Edge.map (BlockEvaluation.global S V n) (edge f)) = _
  rw [NativeTrace.read_global]
  have xh : Edge.map G (idEdge w) = idEdge x := by
    have l := Functor.congr_obj G.asIsomorphism.counit_eq x
    exact (same (NativeCube.ofEq (G.map_id w))).trans (congrArg idEdge l)
  have r := NativeTrace.read_global S U n (idEdge w)
  rw [xh] at r
  unfold grades last
  rw [r]
  apply Prod.ext
  · apply congrArg (NativeTrace.word S n)
    exact (edgePure (endpointOver _ t w)).trans (congrArg idEdge (Functor.congr_obj (actionGrade _ (totalStrong a) (strongOver a)) w))
  · exact (congrArg edge (endpointLeaf _ t w)).trans (reframe _ _ _ _)
end Packed
end ContextualComposition.GrothendieckStep.AmbientCellTrace
