module
public import ContextualComposition.AddressedChartNaturality
public import ContextualComposition.StructuralLinearity
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C}
variable {H : AddStruct S Z} (F : Lin S Z)
/-- Additive monoidal functor diagrams for a gathering functor: reverse
left unitor and reverse associator, with no finite chart in the hypotheses. -/
structure LinMonoidal : Prop where
  unit (a : C) : F.map (H.unitInv a) =
    K.seq (H.unitInv (F.obj a)) (K.seq (S.map F.nil (K.id (F.obj a))) (F.cons Z a))
  assoc (a b c : C) :
    K.seq (S.map (K.id (F.obj a)) (F.cons b c))
      (K.seq (F.cons a (S.obj b c)) (F.map (H.assocInv a b c))) =
      K.seq (H.assocInv (F.obj a) (F.obj b) (F.obj c))
        (K.seq (S.map (F.cons a b) (K.id (F.obj c))) (F.cons (S.obj a b) c))
variable (N : AddNat H) (P : LinMonoidal (H:=H) F)
variable (Q : LinNatural F)
include N P Q in
theorem collect_join {X : Type w} (A : X → C) (xs ys : List X) :
    K.seq (F.collect A (xs ++ ys)) (F.map (join H A xs ys)) =
    K.seq (join H (fun x => F.obj (A x)) xs ys)
      (K.seq (S.map (F.collect A xs) (F.collect A ys)) (F.cons _ _)) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, join, Lin.collect, fold]
    rw [P.unit, ← K.assoc, N.unit, K.assoc, ← K.assoc (S.map _ _), ← S.map_seq, K.id_seq, K.seq_id]
  | cons x xs ih =>
    simp only [List.cons_append, join, Lin.collect, fold]
    rw [F.seq]
    simp only [K.assoc]
    rw [← K.assoc (F.cons _ _), ← F.id (A x), ← Q.bin, K.assoc, ← K.assoc (S.map _ _), ← S.map_seq, ih]
    simp only [F.id, K.id_seq]
    have split {b c d : C} (p : K.Hom b c) (q : K.Hom c d) :
        S.map (K.id (F.obj (A x))) (K.seq p q) =
        K.seq (S.map (K.id _) p) (S.map (K.id _) q) := by
      rw [← S.map_seq, K.id_seq]
    simp only [split, K.assoc, P.assoc]
    rw [← K.assoc (S.map (K.id (F.obj (A x))) (S.map (F.collect A xs) (F.collect A ys))), N.inv]
    simp only [K.assoc]
    rw [← K.assoc (S.map (S.map (K.id (F.obj (A x))) (F.collect A xs)) (F.collect A ys)),
      ← S.map_seq, K.seq_id]

variable {X : Type w} (A : X → C)
mutual
def Branch.distribute (b : Branch X) :
    K.Hom (Branch.obj (S:=S) (Z:=Z) (fun x => F.obj (A x)) b) (F.obj (Branch.obj (S:=S) (Z:=Z) A b)) :=
  match b with
  | .leaf x => F.collect A [x]
  | .rows bs => Branch.distributeRows bs
def Branch.distributeRows (bs : List (Branch X)) :
    K.Hom (Branch.objRows (S:=S) (Z:=Z) (fun x => F.obj (A x)) bs) (F.obj (Branch.objRows (S:=S) (Z:=Z) A bs)) :=
  match bs with
  | [] => F.nil
  | b::bs => K.seq (S.map (Branch.distribute b) (Branch.distributeRows bs)) (F.cons _ _)
end
mutual
theorem Branch.distribute_chart (N : AddNat H) (P : LinMonoidal (H:=H) F) (Q : LinNatural F) (b : Branch X) :
    K.seq (F.collect A b.leaves) (F.map (Branch.chart (H:=H) A b)) =
      K.seq (Branch.chart (H:=H) (fun x => F.obj (A x)) b) (Branch.distribute F A b) := by
  cases b with
  | leaf x =>
    change K.seq (F.collect A [x]) (F.map (K.id _)) = K.seq (K.id _) (F.collect A [x])
    rw [F.id, K.seq_id, K.id_seq]
  | rows bs => exact Branch.distributeRows_chart N P Q bs
theorem Branch.distributeRows_chart (N : AddNat H) (P : LinMonoidal (H:=H) F) (Q : LinNatural F) (bs : List (Branch X)) :
    K.seq (F.collect A (Branch.leavesRows bs)) (F.map (Branch.chartRows (H:=H) A bs)) =
      K.seq (Branch.chartRows (H:=H) (fun x => F.obj (A x)) bs) (Branch.distributeRows F A bs) := by
  cases bs with
  | nil =>
    change K.seq F.nil (F.map (K.id Z)) = K.seq (K.id Z) F.nil
    rw [F.id, K.seq_id, K.id_seq]
  | cons b bs =>
    simp only [Branch.chartRows, Branch.distributeRows, Branch.leavesRows, Branch.objRows, F.seq]
    rw [← K.assoc, collect_join F N P Q, K.assoc, K.assoc, ← Q.bin,
      ← K.assoc (S.map (F.collect A b.leaves) (F.collect A (Branch.leavesRows bs))),
      ← S.map_seq, Branch.distribute_chart N P Q, Branch.distributeRows_chart N P Q,
      S.map_seq, ← K.assoc]
    simp only [K.assoc]
end

/-- The binary additive symmetry diagram for a strong additive gathering. -/
structure LinSymmetric : Prop where
  swap (a b : C) : K.seq (F.cons a b) (F.map (H.swap a b)) =
    K.seq (H.swap (F.obj a) (F.obj b)) (F.cons b a)
variable (Y : LinSymmetric (H:=H) F)
/-- The forward associativity form of the additive monoidal-functor
diagram. Kept separate so a forward-only additive presentation can use
it without first proving the designated associator arrows inverse. -/
structure LinMonoidalForward : Prop where
  assoc (a b c : C) :
    K.seq (S.map (F.cons a b) (K.id (F.obj c)))
      (K.seq (F.cons (S.obj a b) c) (F.map (H.assoc a b c))) =
      K.seq (H.assoc (F.obj a) (F.obj b) (F.obj c))
        (K.seq (S.map (K.id (F.obj a)) (F.cons b c)) (F.cons a (S.obj b c)))
variable (P' : LinMonoidalForward (H:=H) F)
include P P' Q Y in
theorem collect_cross (a b c : C) :
    K.seq (S.map (K.id (F.obj a)) (F.cons b c))
      (K.seq (F.cons a (S.obj b c)) (F.map (movePast H a b c))) =
    K.seq (movePast H (F.obj a) (F.obj b) (F.obj c))
      (K.seq (S.map (K.id (F.obj b)) (F.cons a c)) (F.cons b (S.obj a c))) := by
  unfold movePast
  simp only [F.seq]
  rw [← K.assoc (F.cons _ _), ← K.assoc (S.map _ _) (K.seq _ _), P.assoc]
  simp only [K.assoc]
  rw [← K.assoc (F.cons (S.obj a b) c), ← Q.bin, F.id]
  simp only [K.assoc]
  rw [← K.assoc (S.map (F.cons a b) (K.id _)) (S.map (F.map (H.swap a b)) (K.id _)),
    ← S.map_seq, K.id_seq, Y.swap]
  have h : S.map (K.seq (H.swap (F.obj a) (F.obj b)) (F.cons b a)) (K.id (F.obj c)) =
      K.seq (S.map (H.swap (F.obj a) (F.obj b)) (K.id (F.obj c)))
        (S.map (F.cons b a) (K.id (F.obj c))) := by rw [← S.map_seq, K.id_seq]
  simp only [h, K.assoc, P'.assoc]
include N P P' Q Y in
theorem collect_order (A : X → C) {xs ys : List X} (r : AddressOrder X xs ys) :
    K.seq (F.collect A xs) (F.map (AddressOrder.mapSum H A r)) =
      K.seq (AddressOrder.mapSum H (fun x => F.obj (A x)) r) (F.collect A ys) := by
  induction r with
  | ident => simp only [AddressOrder.mapSum, F.id, K.seq_id, K.id_seq]
  | swap x y ts =>
    simp only [AddressOrder.mapSum, Lin.collect, fold]
    have split {b c d : C} (a : C) (p : K.Hom b c) (q : K.Hom c d) :
        S.map (K.id a) (K.seq p q) =
        K.seq (S.map (K.id a) p) (S.map (K.id a) q) := by rw [← S.map_seq, K.id_seq]
    simp only [split, K.assoc]
    rw [collect_cross F P Q Y P', ← K.assoc (S.map (K.id (F.obj (A x))) (S.map (K.id (F.obj (A y))) (F.collect A ts))), movePast_nat N (K.id (F.obj (A x))) (K.id (F.obj (A y))) (F.collect A ts)]
    simp only [K.assoc]
  | keep x r ih =>
    simp only [AddressOrder.mapSum, Lin.collect, fold]
    rw [K.assoc, ← Q.bin, F.id, ← K.assoc, ← S.map_seq, K.id_seq, ih]
    rw [← K.assoc, ← S.map_seq, K.id_seq]
  | seq r s ih jh =>
    simp only [AddressOrder.mapSum, F.seq, ← K.assoc, ih]
    rw [K.assoc, jh, ← K.assoc]

include N P P' Q Y in
/-- The actual flat-to-branch comparison commutes with gathering for every
addressed permutation and branch tree. This is a derived mixed structural
square for one additive variable of a rig tensor, not endpoint equality. -/
theorem flat_chart_distribution (A : X → C) {xs : List X} (b : Branch X)
    (r : AddressOrder X xs b.leaves) :
    K.seq (F.collect A xs) (F.map (flatToChart (H:=H) A b r)) =
      K.seq (flatToChart (H:=H) (fun x => F.obj (A x)) b r) (Branch.distribute F A b) := by
  unfold flatToChart
  rw [F.seq, ← K.assoc, collect_order F N P Q Y P', K.assoc, Branch.distribute_chart F A N P Q, K.assoc]
end ContextualComposition.NativeFinitePush.DependentFibre
