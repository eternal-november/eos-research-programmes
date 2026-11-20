module
public import ContextualComposition.AmbientNestedGrade
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientChartRows
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport AmbientBicategory AmbientCoordinates ContextadWeakAction AmbientModificationAction
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
universe u v
section Generic
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
theorem rows (U : A ⥤ E) (V : B ⥤ F) (U' : C ⥤ E) (V' : D ⥤ F) [V.IsIso] [V'.IsIso]
    (I : A ⥤ C) (J : B ⥤ D) (u : I ⋙ U' = U) (v : J ⋙ V' = V)
    {T W : E ⥤ F} (n : T ⟶ W) (x : A) :
    Aligned (J.map (V.strictInv.map (n.app (U.obj x)))) (V'.strictInv.map (n.app (U'.obj (I.obj x)))) := by
  let a := n.app (U.obj x)
  have s := (NativeCube.functorAlign v (V.strictInv.map a)).trans (NativeCube.functorAlign V.asIsomorphism.counit_eq a)
  exact (NativeCube.functorAlign V'.asIsomorphism.unit_eq _).trans ((s.trans (ContextadPayloadModification.appChange n (Functor.congr_obj u.symm x))).map V'.strictInv)
theorem alignCancel {K L : Type*} [Category* K] [Category* L] (π : K ⥤ L)
    {a b c a' b' c' : K} {h : a ⟶ b} {j : b ⟶ c} {h' : a' ⟶ b'} {j' : b' ⟶ c'}
    (cart : NativeCleavage.Cartesian π j) (base : Aligned (π.map h) (π.map h')) (right : Aligned j j')
    (sq : Aligned (h ≫ j) (h' ≫ j')) : Aligned h h' := by
  obtain ⟨rfl,rfl,k⟩ := right
  obtain ⟨rfl,_,t⟩ := sq
  simp at k; subst j'
  exact NativeCube.ofEq (cancel π j cart h h' base.eq (by simpa using t))
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell
set_option linter.defProp false in
def split22 :=
  (splitTransport (S := S) X 2 2).trans (selfTransport (G := PackedFree.pow S X 4) (chart S X 4) (PackedCuts.sameLength S X (2,2)).symm)
variable {a b : obj S 4 X ⟶ obj S 2 X}
set_option maxHeartbeats 1500000 in
theorem readNested (t : a ⟶ b) (x : Raw S X 4) :
    Aligned ((stage (S := S) (underlying X) (power S 1)).map (atRaw (X := X) (Y := X) (i := 4) (j := 2) S t x))
      (atRaw (X := obj S 2 X) (Y := obj S 1 X) (i := 2) (j := 1) S t ((splitAt (S := S) (underlying X) 2 2).obj x)) := by
  let n := totalCell t.hom.as
  exact rows (chart S X 4) (chart S X 2) (chart S (obj S 2 X) 2) (chart S (obj S 1 X) 1)
    (splitAt (S := S) (underlying X) 2 2) (stage (S := S) X (power S 1)) (split22 (S := S) X) (resolve1 (S := S) X) n x
end ContextualComposition.GrothendieckStep.AmbientChartRows
