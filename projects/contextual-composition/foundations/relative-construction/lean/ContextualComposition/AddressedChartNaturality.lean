module
public import ContextualComposition.PartitionInverse
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C} {H : AddStruct S Z}
variable (N : AddNat H) {X : Type w} {A B : X → C}
include N in
theorem act_append (p : ∀ x, K.Hom (A x) (B x)) (xs ys : List X) :
    K.seq (act S Z p (xs ++ ys)) (join H B xs ys) =
    K.seq (join H A xs ys) (S.map (act S Z p xs) (act S Z p ys)) := by
  induction xs with
  | nil => exact N.unit _
  | cons x xs ih =>
    simp only [List.cons_append, act, join, fold]
    rw [← K.assoc, ← S.map_seq, K.seq_id, ih, ← K.id_seq (p x), S.map_seq, K.assoc,
      N.inv, K.assoc, K.id_seq]
include N in
theorem AddressOrder.natural (p : ∀ x, K.Hom (A x) (B x))
    {xs ys : List X} (r : AddressOrder X xs ys) :
    K.seq (act S Z p xs) (r.mapSum H B) = K.seq (r.mapSum H A) (act S Z p ys) := by
  induction r with
  | ident => simp only [AddressOrder.mapSum, K.seq_id, K.id_seq]
  | swap => exact movePast_nat N _ _ _
  | keep x r ih => simp only [AddressOrder.mapSum, act, fold, ← S.map_seq, K.seq_id, K.id_seq, ih]
  | seq r s hr hs =>
    simp only [AddressOrder.mapSum, ← K.assoc, hr]
    rw [K.assoc, hs, ← K.assoc]
mutual
def Branch.actChart (p : ∀ x, K.Hom (A x) (B x)) (b : Branch X) :
    K.Hom (Branch.obj (S:=S) (Z:=Z) A b) (Branch.obj (S:=S) (Z:=Z) B b) :=
  match b with
  | .leaf x => act S Z p [x]
  | .rows bs => Branch.actChartRows p bs
def Branch.actChartRows (p : ∀ x, K.Hom (A x) (B x)) (bs : List (Branch X)) :
    K.Hom (Branch.objRows (S:=S) (Z:=Z) A bs) (Branch.objRows (S:=S) (Z:=Z) B bs) :=
  match bs with
  | [] => K.id Z
  | b::bs => S.map (Branch.actChart p b) (Branch.actChartRows p bs)
end
mutual
theorem Branch.chart_natural (N : AddNat H) (p : ∀ x, K.Hom (A x) (B x)) (b : Branch X) :
    K.seq (act S Z p b.leaves) (Branch.chart (H:=H) B b) =
      K.seq (Branch.chart (H:=H) A b) (Branch.actChart p b) := by
  cases b with
  | leaf x => exact (K.seq_id (act S Z p [x])).trans (K.id_seq _).symm
  | rows => exact Branch.chartRows_natural N p _
theorem Branch.chartRows_natural (N : AddNat H) (p : ∀ x, K.Hom (A x) (B x)) (bs : List (Branch X)) :
    K.seq (act S Z p (Branch.leavesRows bs)) (Branch.chartRows (H:=H) B bs) =
      K.seq (Branch.chartRows (H:=H) A bs) (Branch.actChartRows p bs) := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    simp only [Branch.leavesRows, Branch.chartRows, Branch.actChartRows, Branch.objRows]
    rw [← K.assoc, act_append N, K.assoc, ← S.map_seq, Branch.chart_natural N, Branch.chartRows_natural N,
      S.map_seq, ← K.assoc]
end
include N in
theorem flat_chart_natural (p : ∀ x, K.Hom (A x) (B x))
    {xs : List X} (b : Branch X) (r : AddressOrder X xs b.leaves) :
    K.seq (act S Z p xs) (flatToChart (H:=H) B b r) =
    K.seq (flatToChart (H:=H) A b r) (Branch.actChart p b) := by
  unfold flatToChart
  rw [← K.assoc, AddressOrder.natural N, K.assoc, Branch.chart_natural N, K.assoc]
variable (I : AddInvertible H)
def Branch.changeChart (A : X → C) (b c : Branch X) (r : AddressOrder X b.leaves c.leaves) :=
  K.seq (b.chartInv I A).inv (flatToChart (H:=H) A c r)
def Branch.changeChartInv (A : X → C) (b c : Branch X) (r : AddressOrder X b.leaves c.leaves) :
    Inv (Branch.changeChart I A b c r) :=
  (Inv.mk (Branch.chart (H:=H) A b) (b.chartInv I A).ih (b.chartInv I A).hi).comp
    (flatToChartInv I A c r)
include N in
theorem Branch.changeChart_natural (p : ∀ x, K.Hom (A x) (B x))
    (b c : Branch X) (r : AddressOrder X b.leaves c.leaves) :
    K.seq (Branch.actChart p b) (b.changeChart I B c r) =
    K.seq (b.changeChart I A c r) (Branch.actChart p c) := by
  apply (b.chartInv I A).cancelL
  unfold Branch.changeChart
  simp only [← K.assoc]
  rw [← Branch.chart_natural N, K.assoc (act S Z p b.leaves), (b.chartInv I B).hi, K.seq_id,
    (b.chartInv I A).hi, K.id_seq, flat_chart_natural N]
end ContextualComposition.NativeFinitePush.DependentFibre
