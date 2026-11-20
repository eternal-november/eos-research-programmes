module
public import ContextualComposition.AmbientHorizontalRead
public import ContextualComposition.AmbientHorizontalDiagrams
@[expose] public section
namespace ContextualComposition.GrothendieckStep.AmbientDeepIndices
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite TelescopeSquares FibreValue
open AmbientBicategory AmbientCoordinates ContextadModification NativeBlocks CategoryTheory.Bicategory
open ContextadRoutes ContextadNativeLaws ContextadOuterCharts AmbientHorizontalFrames ContextadLawTransport
open ContextadCellWhisker ContextadCellPasting ContextadHorizontalLaws AmbientHorizontalRead ContextadWeakAction ContextadAmbientPayload AmbientHorizontalDiagrams
open scoped CategoryTheory.Pseudofunctor.StrongTrans CategoryTheory.Bicategory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B} {S : P.Split}
variable {X : Obj.{u,v} B} {i j k l : Nat} {r s t : Map S j k}
variable (S) (X) (d : ContextadUnit.Data P) (m : ContextadTotal.Native S)
theorem encodedOfTotal {i j} (a : obj S i X ⟶ obj S j X) (r : Map S i j) (e : tot a = global X r) : encode S a = raw X r :=
  (congrArg (fun z => chart S X i ⋙ z ⋙ (chart S X j).strictInv) e).trans (erase _ _ _)
def chart3 :=
  (splitTransport (S := S) X 1 3).trans (selfTransport (G := PackedFree.pow S X 4) (chart S X 4) (PackedCuts.sameLength S X (1,3)).symm)
section G
variable {A B C D E F : Type*} [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
variable {U : A ⥤ E} {V : B ⥤ F} {J : C ⥤ E} {K : D ⥤ F} [U.IsIso] [J.IsIso]
    {L : A ⥤ C} {M : B ⥤ D} {r : A ⥤ B} {s : C ⥤ D}
theorem joinOf (u : L ⋙ J = U) (v : M ⋙ K = V) (k : r ⋙ M = L ⋙ s) : U.strictInv ⋙ r ⋙ V = J.strictInv ⋙ s ⋙ K := joinChart U V J K L M r s u v k
end G
theorem innerAt {i j : Nat} (v : obj S i X ⟶ obj S j X) (r : Map S i j) (h : global X r = tot v) :
    (chart S (obj S i X) 1).strictInv ⋙ ContextadWeakAction.action (power S 1).dest (global X r) (over X r) ⋙ chart S (obj S j X) 1 = tot (K S v) := by
  apply Eq.trans _ (AmbientBlockIteration.encodedBlock S v.hom 1).symm
  exact congrArg (fun z => (chart S (obj S i X) 1).strictInv ⋙ z ⋙ chart S (obj S j X) 1) (ContextadUnitTotal.congrAction _ _ _ h)
def frontEta :=
  encodedOfTotal S X (i := 2) (j := 3) (K S (E S (obj S 1 X) d)) (inside 1 (leftUnit d)) (
    (joinChart (chart S X 2) (chart S X 3) (chart S (obj S 1 X) 1) (chart S (obj S 2 X) 1)
    (splitAt X 1 1) (splitAt X 1 2) _ _ (splitOne1 X) (splitOne2 X) (splitInside X 1 (leftUnit d))).trans (innerAt S X _ _ (outerE S X d))).symm

def frontMu :=
  encodedOfTotal S X (i := 4) (j := 3) (K S (M S (obj S 1 X) m)) (inside 1 (firstTwo m)) (
    (joinOf (chart3 S X) (splitOne2 (S := S) X) (splitInside X 1 (firstTwo m))).trans (innerAt S X (i := 3) (j := 2) (M S (obj S 1 X) m) (firstTwo m) (outerM S X m))).symm

def deepMuNested :=
  encodedOfTotal S X (i := 4) (j := 3) (K S (K S (M S X m))) (inside 1 (lastTwo m)) (
    (joinOf (chart3 S X) (splitOne2 (S := S) X) (splitInside X 1 (lastTwo m))).trans (innerAt S X (i := 3) (j := 2) (K S (M S X m)) (lastTwo m) (innerM S X m))).symm

def deepMu :=
  (deepMuNested S X m).trans (congrArg (raw (underlying X)) (ContextadSchedule.nested (tensor m)).symm)
end ContextualComposition.GrothendieckStep.AmbientDeepIndices
