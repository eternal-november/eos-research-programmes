module
public import ContextualComposition.AmbientInsideLetters
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientChartSplice
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite FibreValue TelescopeSquares
open ContextadAmbientPayload ContextadWeakAction AmbientBicategory AmbientCoordinates AmbientHorizontalDiagrams
open ContextadRoutes ContextadModification NativeBlocks CategoryTheory.Bicategory ContextadInsideCells ContextadLawTransport
open ContextadOuterCharts ContextadCellWhisker SpanApex AmbientBlockCells AmbientModificationAction AmbientHorizontalFrames AmbientHorizontalRead
open ContextadNativeLaws
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
universe u v
section Charts
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
theorem splice (U : A ⥤ E) (V : B ⥤ F) (U' : C ⥤ E) (V' : D ⥤ F) [V.IsIso] [V'.IsIso]
    (I : A ⥤ C) (J : B ⥤ D) (u : I ⋙ U' = U) (v : J ⋙ V' = V)
    {T W : E ⥤ F} (n : T ⟶ W) (x : A) {b b' : B} (g : b ⟶ b')
    (h : Aligned (V'.strictInv.map (n.app (U'.obj (I.obj x)))) (J.map g)) :
    Aligned (V.strictInv.map (n.app (U.obj x))) g := by
  have h₁ := ContextadPayloadModification.appChange n (Functor.congr_obj u.symm x)
  have h₂ := (NativeCube.functorAlign V'.asIsomorphism.counit_eq.symm _).trans (h.map V')
  exact ((h₁.trans (h₂.trans (NativeCube.functorAlign v g))).map V.strictInv).trans (NativeCube.functorAlign V.asIsomorphism.unit_eq.symm g)
end Charts
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B) {k i j : Nat} {r s : Map S i j} {a b : obj S i X ⟶ obj S j X} (c : Cell r s) (t : a ⟶ b)
theorem atNested (h : Reads t c) (ha : tot a = global X r) (hb : tot b = global X s) (x) :
    Aligned (atRaw S (cell S k t) ((splitAt X k i).obj x)) ((splitAt X k j).map ((rawCell X (insideCell k c)).hom.app x)) :=
  (AmbientComparisonRead.modAt S t k _).trans (AmbientInsideLetters.splitRead X k c t h ha hb x).symm
variable (d : ContextadUnit.Data P) (m : ContextadTotal.Native S) (C : Constraints d m)
theorem totalRoute {i j k} (v : obj S i X ⟶ obj S j X) (r : Map S i j) (s : Map S j k) (q : gradeCart s)
    (h : global X r = tot v) : tot (v ≫ oper S s q X) = global X (comp r s) :=
  (totalAfter _ _).trans ((congrArg₂ (· ⋙ ·) h.symm (totalOper S X s q)).trans (globalComp X r s))
end ContextualComposition.GrothendieckStep.AmbientChartSplice
