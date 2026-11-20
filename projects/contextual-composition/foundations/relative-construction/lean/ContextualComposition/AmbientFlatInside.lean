module
public import ContextualComposition.AmbientChartRows
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientFlatInside
open CategoryTheory CategoryTheory.Functor Opposite SpanApex NativeBlocks FibreValue TelescopeSquares
open ContextadRoutes ContextadOuterCharts ContextadLawTransport AmbientBicategory AmbientCoordinates ContextadWeakAction AmbientModificationAction
open AmbientHorizontalRead AmbientHorizontalFrames ContextadInsideCells
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
universe u v
section Generic
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
theorem rechart (U : A ⥤ E) (V : B ⥤ F) (U' : C ⥤ E) (V' : D ⥤ F) [V.IsIso] [V'.IsIso]
    (I : A ⥤ C) (J : B ⥤ D) (u : I ⋙ U' = U) (v : J ⋙ V' = V)
    {T W : E ⥤ F} (n : T ⟶ W) {R S : A ⥤ B} (c : R ⟶ S)
    (h : ∀ x, Aligned (V'.strictInv.map (n.app (U'.obj (I.obj x)))) (J.map (c.app x))) :
    ∀ x, Aligned (V.strictInv.map (n.app (U.obj x))) (c.app x) :=
  fun x => AmbientChartSplice.splice U V U' V' I J u v n x _ (h x)
end Generic
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable (X : Obj.{u,v} B)
attribute [local irreducible] BlockEvaluation.global ContextadAmbientPayload.totalStrong AmbientModificationAction.totalCell ContextadLawTransport.rawCell ContextadInsideCells.insideCell
section Letters
variable {k i j : Nat} {r s : Map S i j} {a b : obj S i X ⟶ obj S j X} (c : Cell r s) (t : a ⟶ b)
set_option linter.defProp false in
def flat (h : Reads (X := X) t c) (ha : tot a = global X r) (hb : tot b = global X s)
    (F : Raw S X (k+i) ⥤ Total (underlying (obj S k (obj S i X))) (𝟭 B))
    (G : Raw S X (k+j) ⥤ Total (underlying (obj S k (obj S j X))) (𝟭 B)) [G.IsIso]
    (u : splitAt (S := S) (underlying X) k i ⋙ chart S (obj S i X) k = F)
    (v : splitAt (S := S) (underlying X) k j ⋙ chart S (obj S j X) k = G) :=
  let n := totalCell (cell S k t).hom.as
  let w := (rawCell (underlying X) (insideCell k c)).hom
  let z := AmbientChartSplice.atNested (S := S) X (k := k) (r := r) (s := s) (a := a) (b := b) c t h ha hb
  rechart F G (chart S (obj S i X) k) (chart S (obj S j X) k)
    (splitAt (S := S) X k i) (splitAt (S := S) X k j) u v n w z
end Letters
section One
variable {r s : Map S 1 1} {a b : obj S 1 X ⟶ obj S 1 X} (c : Cell r s) (t : a ⟶ b)
set_option linter.defProp false in
def unitLetter (h : Reads (X := X) t c) (ha : tot a = global X r) (hb : tot b = global X s) :=
  flat (S := S) X (a := a) (b := b) (k := 1) c t h ha hb (chart S X 2) (chart S X 2)
    (splitOne1 (S := S) X) (splitOne1 (S := S) X)
end One
section Three
variable {r s : Map S 3 1} {a b : obj S 3 X ⟶ obj S 1 X} (c : Cell r s) (t : a ⟶ b)
set_option linter.defProp false in
def assocLetter (h : Reads (X := X) t c) (ha : tot a = global X r) (hb : tot b = global X s) :=
  flat (S := S) X (a := a) (b := b) (k := 1) c t h ha hb (chart S X 4) (chart S X 2)
    (AmbientDeepIndices.chart3 S X) (splitOne1 (S := S) X)
end Three
end ContextualComposition.GrothendieckStep.AmbientFlatInside
