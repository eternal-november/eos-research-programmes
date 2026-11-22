module
public import ContextualComposition.RaggedFubini
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
structure LinNatural (F : Lin S Z) : Prop where
  bin {a b c d : C} (p : K.Hom a c) (q : K.Hom b d) :
    K.seq (S.map (F.map p) (F.map q)) (F.cons c d) =
      K.seq (F.cons a b) (F.map (S.map p q))
theorem Lin.collect_comp (F G : Lin S Z) (N : LinNatural G) {X : Type w}
    (A : X → C) (xs : List X) :
    (F.comp G).collect A xs =
      K.seq (G.collect (fun x => F.obj (A x)) xs) (G.map (F.collect A xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Lin.collect, Lin.comp, fold, K.assoc, ih, G.seq]
    rw [← K.id_seq (K.id (G.obj (F.obj (A x)))), G.id (F.obj (A x)) |>.symm, S.map_seq]
    simp only [K.assoc]
    rw [← K.assoc (S.map (G.map _) (G.map _)), N.bin]
    simp only [K.assoc, G.id, K.id_seq]
theorem Lin.collect_nat (F : Lin S Z) (N : LinNatural F) {X : Type w}
    {A B : X → C} (p : ∀ x, K.Hom (A x) (B x)) (xs : List X) :
    K.seq (act S Z (fun x => F.map (p x)) xs) (F.collect B xs) =
    K.seq (F.collect A xs) (F.map (act S Z p xs)) := by
  induction xs with
  | nil => simp only [act, fold, Lin.collect, F.id, K.id_seq, K.seq_id]
  | cons x xs ih =>
    simp only [act, Lin.collect, fold]
    rw [← K.assoc, ← S.map_seq, K.seq_id, ih,
      ← K.id_seq (F.map (p x)), ← F.id, S.map_seq, K.assoc, N.bin]
    simp only [K.assoc, F.id]

theorem rightNatural (G : Gather S T Z) (N : GatherOuterNat G) (a : C) :
    LinNatural (Lin.right G a) := ⟨fun p q => N.cons p q a⟩
structure GatherLeftNat (L : LeftGather S T Z) : Prop where
  inner (a : C) : LinNatural (Lin.left L a)
  outer {a b : C} (p : K.Hom a b) :
    LinSquare (Lin.left L a) (Lin.left L b) (fun x => T.map p (K.id x))
theorem rightLinear (G : Gather S T Z) {a b : C} (q : K.Hom a b) :
    LinSquare (Lin.right G a) (Lin.right G b) (fun x => T.map (K.id x) q) :=
  ⟨G.nil_nat q,fun x y => G.cons_nat x y q⟩

variable (G : Gather S T Z) (L : LeftGather S T Z)
variable (Ng : GatherOuterNat G) (Nl : GatherLeftNat L)
variable {X Y : Type w} (V : X → C) (W : Y → C) (xs : List X) (ys : List Y) (b d : C)
def nativeRight :=
  K.seq (act S Z (fun x =>
    (Lin.right G (T.obj b d)).collect (fun y => T.obj (V x) (W y)) ys) xs)
    (K.seq ((Lin.right G (T.obj b d)).collect
      (fun x => fold S Z (fun y => T.obj (V x) (W y)) ys) xs)
      (T.map (rect G L V W xs ys) (K.id (T.obj b d))))
include Ng in
theorem right_reduction :
    rhsGather G L V W xs ys b d = nativeRight G L V W xs ys b d := by
  unfold rhsGather nativeRight rect
  simp only [rightY, rightX, Lin.collect_comp _ _ (rightNatural G Ng _)]
  rw [← act_seq, K.assoc]
  rw [← K.assoc (act S Z (fun x => (Lin.right G (T.obj b d)).map _ ) xs)]
  rw [Lin.collect_nat _ (rightNatural G Ng _)]
  simp only [K.assoc, ← T.map_seq, K.id_seq]
  have hL (a : C) : (Lin.left L a).collect W ys = innerLeft L a W ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [Lin.collect, innerLeft, ih]
  have hR : (Lin.right G (fold S Z W ys)).collect V xs = gather G V (fold S Z W ys) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [Lin.collect, gather, ih]
  simp only [hL, hR]

/-- Literal row-major tensor product of the two individual factorizations.
The right coordinate is gathered on each row, then the left coordinate
is gathered while the whole right sum stays fixed. -/
def nativeLeft :=
  K.seq (act S Z (fun x =>
    (Lin.left L (T.obj (V x) b)).collect (fun y => T.obj (W y) d) ys) xs)
    (K.seq ((Lin.right G (fold S Z (fun y => T.obj (W y) d) ys)).collect (fun x => T.obj (V x) b) xs)
      (T.map ((Lin.right G b).collect V xs) ((Lin.right G d).collect W ys)))
include Ng Nl in
theorem left_reduction :
    lhsGather G L V W xs ys b d = nativeLeft G L V W xs ys b d := by
  unfold lhsGather nativeLeft
  simp only [leftY, leftX, Lin.collect_comp _ _ (Nl.inner _),
    Lin.collect_comp _ _ (rightNatural G Ng _)]
  rw [← act_seq, K.assoc]
  rw [← K.assoc (act S Z (fun x => (Lin.left L (T.obj (V x) b)).map _) xs)]
  rw [← (rightLinear G _).collect (fun x => T.obj (V x) b) xs]
  simp only [K.assoc]
  rw [← T.map_seq, K.id_seq, K.seq_id]
variable (a c : C) (bs ds : List C)
def separateInnerNative :=
  K.seq (act S Z (fun b =>
    (Lin.left L (T.obj a b)).collect (T.obj c) ds) bs)
    (K.seq ((Lin.right G (fold S Z (T.obj c) ds)).collect (T.obj a) bs)
      (T.map ((Lin.left L a).collect id bs) ((Lin.left L c).collect id ds)))
def togetherInnerNative :=
  K.seq (act S Z (fun b =>
    (Lin.left L (T.obj a c)).collect (T.obj b) ds) bs)
    (K.seq ((Lin.left L (T.obj a c)).collect (fun b => fold S Z (T.obj b) ds) bs)
      (T.map (K.id (T.obj a c)) (rect G L id id bs ds)))
include Ng Nl in
theorem inner_left_reduction :
    lhsInner G L a c bs ds = separateInnerNative G L a c bs ds := by
  unfold lhsInner separateInnerNative
  simp only [lhsD, lhsB, Lin.collect_comp _ _ (Nl.inner _),
    Lin.collect_comp _ _ (rightNatural G Ng _), id_eq]
  rw [← act_seq, K.assoc]
  rw [← K.assoc (act S Z (fun x => (Lin.left L (T.obj a x)).map _) bs)]
  rw [← (rightLinear G _).collect (T.obj a) bs]
  simp only [K.assoc]
  rw [← T.map_seq, K.id_seq, K.seq_id]
  rfl
include Nl in
theorem inner_right_reduction :
    rhsInner G L a c bs ds = togetherInnerNative G L a c bs ds := by
  unfold rhsInner togetherInnerNative rect
  simp only [rhsD, rhsB, Lin.collect_comp _ _ (Nl.inner _), id_eq]
  rw [← act_seq, K.assoc]
  rw [← K.assoc (act S Z (fun x => (Lin.left L (T.obj a c)).map _) bs)]
  rw [Lin.collect_nat _ (Nl.inner _)]
  simp only [K.assoc, ← T.map_seq, K.id_seq]
  have hL (x : C) : (Lin.left L x).collect id ds = innerLeft L x id ds := by
    induction ds with
    | nil => rfl
    | cons y ys ih => simp only [Lin.collect, innerLeft, ih]
  have hR : (Lin.right G (fold S Z id ds)).collect id bs = gather G id (fold S Z id ds) bs := by
    induction bs with
    | nil => rfl
    | cons x xs ih => simp only [Lin.collect, gather, ih]
  simp only [hL, hR]
  rfl

include Ng Nl in
/-- Comparison of independently specified distributor factorizations, before
normalizing their separately gathered factors. The common source is still
the row-major branch chart, not an arbitrary chosen flat Fin enumeration. -/
theorem native_binary_on_chart {U : C} (M : Middle T U)
    (H : MedialLinear M G L) (Q : MedialInner M G L)
    (B : X → List C) (D : Y → List C)
    (β : ∀ x, K.Hom (fold S Z id (B x)) b) (θ : ∀ y, K.Hom (fold S Z id (D y)) d)
    {a' c' : C} (α : K.Hom (fold S Z V xs) a') (γ : K.Hom (fold S Z W ys) c') :
    K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => separateInnerNative G L (V x) (W y) (B x) (D y)))
      (K.seq (actRect (S:=S) (Z:=Z) xs ys
        (fun x y => T.map (T.map (K.id (V x)) (β x)) (T.map (K.id (W y)) (θ y))))
        (K.seq (nativeLeft G L V W xs ys b d)
          (K.seq (T.map (T.map α (K.id b)) (T.map γ (K.id d))) (M.cell a' b c' d)))) =
    K.seq (actRect (S:=S) (Z:=Z) xs ys
      (fun x y => actRect (S:=S) (Z:=Z) (B x) (D y) (fun v w => M.cell (V x) v (W y) w)))
      (K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => togetherInnerNative G L (V x) (W y) (B x) (D y)))
        (K.seq (actRect (S:=S) (Z:=Z) xs ys
          (fun x y => T.map (T.map (K.id (V x)) (K.id (W y))) (T.map (β x) (θ y))))
          (K.seq (nativeRight G L V W xs ys b d) (T.map (T.map α γ) (T.map (K.id b) (K.id d)))))) := by
  have h := ragged_binary M G L V W xs ys B D b d β θ α γ H Q
  unfold separate together at h
  rw [left_reduction G L Ng Nl, right_reduction G L Ng] at h
  simpa only [inner_left_reduction G L Ng Nl, inner_right_reduction G L Nl] using h
end ContextualComposition.NativeFinitePush.DependentFibre
