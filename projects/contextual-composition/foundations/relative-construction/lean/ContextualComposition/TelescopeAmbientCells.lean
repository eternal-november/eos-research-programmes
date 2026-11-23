module
public import ContextualComposition.TelescopeAmbientComponents
public import ContextualComposition.AmbientCellTrace
public import ContextualComposition.TelescopeEvaluationModification

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientCells
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open ContextadAmbientPayload AmbientBicategory AmbientCoordinates AmbientBlockCells
open AmbientModificationAction AmbientCellFunctor AmbientCellTrace NativeBlocks WordTrace
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) {X Y : Obj.{u,v} B} {a b : X ⟶ Y} (m : a ⟶ b)

/-- A directed ambient modification on an independent iterate retains its entire native weighted cell under the global chart. -/
theorem chart_cell (n : Nat) (x : Total (underlying X) (power S n).dest) :
    edge ((totalCell (blockMod S m.hom.as n)).app ((chart S X n).obj x)) =
      Edge.map (chart S Y n) (edge ((endpointCell (power S n).dest m.hom.as).app x)) := by
  rw [show edge ((totalCell (blockMod S m.hom.as n)).app ((chart S X n).obj x)) = _ from
    decoded _ _ _ _ _ _ (blockPres S a.hom n) (blockPres S b.hom n) ((chart S X n).obj x)]
  let G := chart S X n
  let Q := fun z => Edge.map (chart S Y n) (edge ((endpointCell (power S n).dest m.hom.as).app z))
  exact congrArg Q (Functor.congr_obj G.asIsomorphism.unit_eq.symm x)

section Edges
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

private theorem reflect_edge (J : D ⥤ E) [J.Faithful] (inj : Function.Injective J.obj) :
    Function.Injective (Edge.map J) := by
  rintro ⟨x,y,f⟩ ⟨p,q,g⟩ h
  obtain rfl : x = p := inj (congrArg Edge.src h)
  obtain rfl : y = q := inj (congrArg Edge.dst h)
  exact congrArg (fun j : x ⟶ y => edge j) (J.map_injective (eq_of_heq (Edge.hom_heq h)))

private theorem edge_of_square {F G F' G' : C ⥤ D} (p : F = F') (q : G = G') (l : F ⟶ G) (r : F' ⟶ G')
    (h : l ≫ eqToHom q = eqToHom p ≫ r) (x : C) : edge (l.app x) = edge (r.app x) := by
  subst F'; subst G'
  have hr : l = r := by simpa using h
  rw [hr]

private theorem square_of_edge {F G F' G' : C ⥤ D} (p : F = F') (q : G = G') (l : F ⟶ G) (r : F' ⟶ G')
    (h : ∀ x, edge (l.app x) = edge (r.app x)) : l ≫ eqToHom q = eqToHom p ≫ r := by
  subst F'; subst G'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply NatTrans.ext
  funext x
  exact eq_of_heq (Edge.hom_heq (h x))

end Edges
open CoproductSpan CoproductSpan.All TelescopeAmbientComponents

/-- The cell used by the independently defined ambient action on the nth iterate at base A. -/
noncomputable abbrev targetCell (A : B) (n : Nat) := ((AmbientBicategory.cell S n m).hom.as.app ⟨op A⟩).toNatTrans

set_option maxHeartbeats 500000 in
theorem component_edges (A : B) (n : Nat) (x : Total (underlying X) (leg (src S) (dst S) A n)) :
    edge ((targetCell S m A n).app ((component S (underlying X) A n).functor.obj x)) =
      Edge.map (component S (underlying Y) A n).functor (edge ((endpointCell (leg (src S) (dst S) A n) m.hom.as).app x)) := by
  let H := PackedFree.pow S (underlying Y) n
  let I := FibreValue.incl H A
  let _ : I.Faithful := (inferInstance : (FibreValue.embed H A ⋙ Functor.Fiber.fiberInclusion).Faithful)
  have inj : Function.Injective I.obj := by
    intro z z' eq
    exact (Sigma.mk.inj_iff.mp (congrArg (BlockEvaluation.totalPoints H (𝟭 B)) eq)).2.eq
  apply reflect_edge I inj
  let cx := (component S (underlying X) A n).functor
  let sx := SpanPayload.Power.fibreInclude A (underlying X) (power S n).source (power S n).dest
  let sy := SpanPayload.Power.fibreInclude A (underlying Y) (power S n).source (power S n).dest
  let z := (FibreValue.incl (PackedFree.pow S (underlying X) n) A).obj (cx.obj x)
  let u := edge ((endpointCell (leg (src S) (dst S) A n) m.hom.as).app x)
  have start : Edge.map I (edge ((targetCell S m A n).app (cx.obj x))) =
      edge ((totalCell (blockMod S m.hom.as n)).app z) :=
    congrArg edge (totalApp (blockMod S m.hom.as n) z).symm
  have mid : edge ((endpointCell (power S n).dest m.hom.as).app (sx.obj x)) = Edge.map sy u :=
    edge_of_square _ _ _ _ (TelescopeGradeChange.totalMap_modification m.hom.as
      (Functor.Fiber.fiberInclusion (p := (power S n).source) (S := A)) (power S n).dest rfl) x
  exact start.trans ((congrArg (fun z => edge ((totalCell (blockMod S m.hom.as n)).app z))
        (Functor.congr_obj (component_incl S A (underlying X) n) x)).trans
    ((chart_cell S m n (sx.obj x)).trans ((congrArg (Edge.map (chart S Y n)) mid).trans
      (congrArg (fun J => Edge.map J u) (component_incl S A (underlying Y) n).symm))))

/-- The comparison square on each length is natural in every directed modification of ambient strong maps. -/
theorem component_modification (A : B) (n : Nat) :
    whiskerLeft (component S (underlying X) A n).functor (targetCell S m A n) ≫
      eqToHom (component_payload S A b n) =
    eqToHom (component_payload S A a n) ≫
      whiskerRight (endpointCell (leg (src S) (dst S) A n) m.hom.as) (component S (underlying Y) A n).functor :=
  square_of_edge _ _ _ _ (component_edges S m A n)

/-- The actual assembled telescope comparison is natural in every directed ambient payload modification, at any fixed base object. -/
theorem evaluation_modification (A : B) :
    TelescopeGradeChange.SquareNaturality (evaluation_payload S A a) (evaluation_payload S A b)
      (endpointCell (wholeLeg (src S) (dst S) A) m.hom.as) (Sigma.natTrans.sigma (targetCell S m A)) :=
  TelescopeGradeChange.evaluation_modification_of_components S A m.hom.as
    (target S A a) (target S A b) (fun n => eqToIso (component_payload S A a n))
    (fun n => eqToIso (component_payload S A b n)) (targetCell S m A) (component_modification S m A)

end ContextualComposition.GrothendieckStep.TelescopeAmbientCells
