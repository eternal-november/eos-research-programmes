module
public import ContextualComposition.FlatJoinCoherence
@[expose] public section
/-! Compare the two actual distributor orders with two dependent branch axes.
The result concerns the resource maps, not just enumeration of carriers. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
variable (M : AddCross S Z) (R : Gather S T Z) (L : LeftGather S T Z)
variable (N : GridBinary M R L)
variable {X U Y W : Type u}
variable (A : X → U → C) (B : Y → W → C)
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
def aSum (x : X) := fold S Z (A x) (us x)
def bSum (y : Y) := fold S Z (B y) (vs y)
/-- The occurrence-first sum has order x,u,y,v. Gather the entire second
occurrence against each actual coefficient from the first, then gather
the two remaining outer axes. -/
def occurrenceFirst :=
  K.seq (act S Z (fun x => raggedRowGather R L (A x) (us x) ys vs B) xs)
    (gather R (aSum (S:=S) (Z:=Z) A us) (fold S Z (bSum (S:=S) (Z:=Z) B vs) ys) xs)
/-- The joint order is x,y,u,v. Gather each actual ragged inner rectangle,
then gather the outer rectangle. -/
def outerFirst :=
  K.seq (act S Z (fun x => act S Z (fun y => rowGather R L (A x) (B y) (us x) (vs y)) ys) xs)
    (rowGather R L (aSum (S:=S) (Z:=Z) A us) (bSum (S:=S) (Z:=Z) B vs) xs ys)
def exchangeInner :=
  act S Z (fun x => transposeBlock M (raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B) ys (us x)) xs
include N in
theorem occurrence_outer :
    K.seq (exchangeInner (T:=T) M A B xs ys us vs) (outerFirst R L A B xs ys us vs) =
      occurrenceFirst R L A B xs ys us vs := by
  unfold exchangeInner outerFirst occurrenceFirst rowGather
  rw [← K.assoc, act_seq, ← K.assoc, act_seq]
  simp only [K.assoc]
  change K.seq (act S Z (fun x => K.seq (transposeBlock M (raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B) ys (us x))
    (raggedColGather R L (A x) (us x) ys vs B)) xs) _ = _
  congr 1
  congr 1
  funext x
  exact ragged_interchange M R L N (A x) (us x) ys vs B

include N in
/-- The postcomposition can apply both original whole dependent-pair
maps in parallel, including aggregators on empty fibres. -/
theorem occurrence_outer_native {a b : C}
    (p : K.Hom (fold S Z (aSum (S:=S) (Z:=Z) A us) xs) a)
    (q : K.Hom (fold S Z (bSum (S:=S) (Z:=Z) B vs) ys) b) :
    K.seq (exchangeInner (T:=T) M A B xs ys us vs) (K.seq (outerFirst R L A B xs ys us vs) (T.map p q)) =
      K.seq (occurrenceFirst R L A B xs ys us vs) (T.map p q) := by
  rw [← K.assoc, occurrence_outer M R L N]

section Naturality
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable {V V' : X → C} {W W' : Y → C}
include NL in
theorem left_collect_both (x x' : C) (p : K.Hom x x') (q : ∀ y, K.Hom (W y) (W' y)) :
    K.seq (act S Z (fun y => T.map p (q y)) ys) ((Lin.left L x').collect W' ys) =
      K.seq ((Lin.left L x).collect W ys) (T.map p (act S Z q ys)) := by
  have e : (fun y => T.map p (q y)) =
      fun y => K.seq (T.map p (K.id (W y))) (T.map (K.id x') (q y)) := by
    funext y
    rw [← T.map_seq, K.seq_id, K.id_seq]
  rw [e, ← act_seq, K.assoc, Lin.collect_nat _ (NL.inner x'), ← K.assoc]
  rw [← (NL.outer p).collect W ys, K.assoc, ← T.map_seq, K.seq_id, K.id_seq]

include NR NL in
theorem rowGather_nat (p : ∀ x, K.Hom (V x) (V' x)) (q : ∀ y, K.Hom (W y) (W' y)) :
    K.seq (act S Z (fun x => act S Z (fun y => T.map (p x) (q y)) ys) xs) (rowGather R L V' W' xs ys) =
      K.seq (rowGather R L V W xs ys) (T.map (act S Z p xs) (act S Z q ys)) := by
  unfold rowGather tally
  rw [← K.assoc, act_seq]
  simp only [left_collect_both L ys NL]
  rw [← act_seq, K.assoc]
  have e : (fun x => T.map (p x) (act S Z q ys)) =
      fun x => K.seq (T.map (K.id (V x)) (act S Z q ys)) (T.map (p x) (K.id (fold S Z W' ys))) := by
    funext x
    rw [← T.map_seq, K.id_seq, K.seq_id]
  rw [e, ← act_seq, K.assoc, gather_outer NR]
  simp only [K.assoc]
  rw [← K.assoc (act S Z (fun x => T.map (K.id (V x)) (act S Z q ys)) xs), ← gather_nat, K.assoc,
    ← T.map_seq, K.id_seq, K.seq_id]
end Naturality

section NativeLeft
variable {M₀ : Middle T Z}
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
theorem collect_right_eq {I : Type w} (V : I → C) (is : List I) (c : C) :
    (Lin.right R c).collect V is = gather R V c is := by
  induction is with
  | nil => rfl
  | cons x xs ih => simp only [Lin.collect, gather, ih]
theorem collect_left_eq (a : C) (us : List C) :
    (Lin.left L a).collect id us = gatherLeft L a us := by
  induction us with
  | nil => rfl
  | cons x xs ih => simp only [Lin.collect, gatherLeft, ih, id_eq]

variable (V : X → C) (W : Y → C) (J : Input X C) (P : Input Y C)
variable {b d : C}
variable (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b)
variable (θ : ∀ y, K.Hom (inner (S:=S) (Z:=Z) P y) d)
theorem inner_occurrence_reduction (x : X) (y : Y) :
    K.seq (rowGather R L (T.obj (V x)) (T.obj (W y)) (J.terms x) (P.terms y))
      (T.map (row V J L β x) (row W P L θ y)) =
      K.seq (separateInnerNative R L (V x) (W y) (J.terms x) (P.terms y))
        (T.map (T.map (K.id (V x)) (β x)) (T.map (K.id (W y)) (θ y))) := by
  unfold row separateInnerNative rowGather tally
  rw [T.map_seq, ← K.assoc, K.assoc]
  simp only [collect_right_eq, collect_left_eq, K.assoc]

variable {a c : C} (α : K.Hom (fold S Z V xs) a) (γ : K.Hom (fold S Z W ys) c)
variable {I : C} (m : Middle T I)
include NR NL in
theorem separate_is_native :
    K.seq (outerFirst R L (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys J.terms P.terms)
      (K.seq (T.map (dep R V J L xs β α) (dep R W P L ys θ γ)) (m.cell a b c d)) =
    separate m R L V W xs ys J.terms P.terms b d β θ α γ := by
  unfold outerFirst separate dep
  simp only [T.map_seq, K.assoc]
  rw [← K.assoc (rowGather _ _ _ _ _ _), ← rowGather_nat R L xs ys NR NL]
  simp only [K.assoc]
  rw [← K.assoc (act S Z (fun x => act S Z (fun y => rowGather R L (T.obj (V x)) (T.obj (W y)) (J.terms x) (P.terms y)) ys) xs), act_seq]
  simp only [act_seq, inner_occurrence_reduction R L V W J P β θ]
  simp only [← act_seq, K.assoc, actRect]
  simp only [inner_left_reduction R L NR NL, left_reduction R L NR NL]
  unfold nativeLeft rowGather tally
  simp only [collect_right_eq, K.assoc]
end NativeLeft

section NativeRight
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
theorem rect_is_row {X Y : Type w} (A : X → C) (B : Y → C) (xs : List X) (ys : List Y) :
    rect R L A B xs ys = rowGather R L A B xs ys := by
  have hx (x : X) : innerLeft L (A x) B ys = (Lin.left L (A x)).collect B ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [innerLeft, Lin.collect, ih]
  simp only [rect, rowGather, tally, hx]
variable (V : X → C) (W : Y → C) (J : Input X C) (P : Input Y C)
variable {b d : C}
variable (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b)
variable (θ : ∀ y, K.Hom (inner (S:=S) (Z:=Z) P y) d)
variable {a c : C} (α : K.Hom (fold S Z V xs) a) (γ : K.Hom (fold S Z W ys) c)
variable {I : C} (m : Middle T I)

/-- Actual independent aggregation over two whole fibres, without any
coproduct universal property. -/
def independentCell {E F : Type w} (a : E → C) (b : F → C)
    (es : List E) (fs : List F) {c d : C}
    (p : K.Hom (fold S Z a es) c) (q : K.Hom (fold S Z b fs) d) :=
  K.seq (rowGather R L a b es fs) (T.map p q)

/-- Compress the ragged coefficient tensor at a fixed pair of source
parents; its two continuation maps have whole source fibres. -/
def jointInnerCell (x : X) (y : Y) :=
  let A := T.obj (V x) (W y)
  let bs := J.terms x
  let ds := P.terms y
  K.seq (act S Z (fun v => (Lin.left L A).collect (T.obj v) ds) bs)
    (K.seq ((Lin.left L A).collect (fun v => fold S Z (T.obj v) ds) bs)
      (T.map (K.id A) (independentCell R L id id bs ds (β x) (θ y))))

def jointOuterCell :=
  K.seq (act S Z (fun x =>
    (Lin.right R (T.obj b d)).collect (fun y => T.obj (V x) (W y)) ys) xs)
    (K.seq ((Lin.right R (T.obj b d)).collect
      (fun x => fold S Z (fun y => T.obj (V x) (W y)) ys) xs)
      (T.map (independentCell R L V W xs ys α γ) (K.id (T.obj b d))))
/-- The joint route, defined from the two native independent cells (inner
and outer), with addressed leaf shuffle and continuations before parents. -/
def jointNative :=
  K.seq (actRect (S:=S) (Z:=Z) xs ys
    (fun x y => actRect (S:=S) (Z:=Z) (J.terms x) (P.terms y) (fun u v => m.cell (V x) u (W y) v)))
    (K.seq (actRect (S:=S) (Z:=Z) xs ys (jointInnerCell R L V W J P β θ))
      (jointOuterCell (b:=b) (d:=d) R L xs ys V W α γ))

include NR NL in
theorem together_is_native :
    together m R L V W xs ys J.terms P.terms b d β θ α γ =
      jointNative R L xs ys V W J P β θ α γ m := by
  have hInner (x : X) (y : Y) :
      K.seq (togetherInnerNative R L (V x) (W y) (J.terms x) (P.terms y))
        (T.map (T.map (K.id (V x)) (K.id (W y))) (T.map (β x) (θ y))) =
      jointInnerCell R L V W J P β θ x y := by
    unfold togetherInnerNative jointInnerCell independentCell
    simp only [rect_is_row, T.map_id, K.assoc]
    rw [← T.map_seq, K.id_seq]
  have hOuter :
      K.seq (nativeRight R L V W xs ys b d)
        (T.map (T.map α γ) (T.map (K.id b) (K.id d))) =
      jointOuterCell (b:=b) (d:=d) R L xs ys V W α γ := by
    unfold nativeRight jointOuterCell independentCell
    simp only [rect_is_row, T.map_id, K.assoc]
    rw [← T.map_seq, K.id_seq]
  unfold together jointNative
  simp only [inner_right_reduction R L NL, right_reduction R L NR]
  rw [← K.assoc (actRect xs ys (fun x y => togetherInnerNative R L (V x) (W y) (J.terms x) (P.terms y))),
    actRect_seq]
  simp only [hInner,hOuter]
end NativeRight

section BinaryComparison
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (V : X → C) (W : Y → C) (J : Input X C) (P : Input Y C)
variable {b d : C}
variable (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b)
variable (θ : ∀ y, K.Hom (inner (S:=S) (Z:=Z) P y) d)
variable {a c : C} (α : K.Hom (fold S Z V xs) a) (γ : K.Hom (fold S Z W ys) c)
variable {I : C} (m : Middle T I)

include N NR NL in
/-- Binary fixed-final-fibre Fubini for the actual two native coefficient
routes, on the occurrence-first four-level chart. One route tensors the
two dependent whole-fibre maps; the other builds and uses the independent
inner and outer native maps, interposing the leaf shuffle. -/
theorem binary_native_routes (H : MedialLinear m R L) (Q : MedialInner m R L) :
    K.seq (occurrenceFirst R L (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys J.terms P.terms)
      (K.seq (T.map (dep R V J L xs β α) (dep R W P L ys θ γ)) (m.cell a b c d)) =
    K.seq (exchangeInner (T:=T) M (fun x => T.obj (V x)) (fun y => T.obj (W y)) xs ys J.terms P.terms)
      (jointNative R L xs ys V W J P β θ α γ m) := by
  rw [← occurrence_outer M R L N, K.assoc, separate_is_native R L xs ys NR NL,
    ragged_binary m R L V W xs ys J.terms P.terms b d β θ α γ H Q, together_is_native R L xs ys NR NL]
end BinaryComparison

namespace GridCircuit
variable {I Zx : Type w}
def foreach (a b : Zx → GridExpr I) (p : ∀ z, GridCircuit I (a z) (b z)) : (zs : List Zx) →
    GridCircuit I (GridExpr.over a zs) (GridExpr.over b zs)
  | [] => .ident _
  | z::zs => .bin (p z) (foreach a b p zs)
theorem foreach_eval (V : I → C) (a b : Zx → GridExpr I)
    (p : ∀ z, GridCircuit I (a z) (b z)) (zs : List Zx) :
    HEq (GridCircuit.eval M V (foreach a b p zs))
      (act S Z (fun z => GridCircuit.eval M V (p z)) zs) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [foreach, GridCircuit.eval, act]
    exact structural_map_heq rfl rfl (GridExpr.eval_over V a zs) (GridExpr.eval_over V b zs) HEq.rfl ih
end GridCircuit

section Chart
def quadLabels (p : X × U × Y × W) := T.obj (A p.1 p.2.1) (B p.2.2.1 p.2.2.2)
def innerQuad (x : X) (y : Y) (u : U) :=
  GridExpr.over (fun v => .leaf (x,u,y,v)) (vs y)
def fourOccurrenceExpr :=
  GridExpr.over (fun x => GridExpr.over (fun u => GridExpr.over (fun y => innerQuad vs x y u) ys) (us x)) xs
def fourJointExpr :=
  GridExpr.over (fun x => GridExpr.over (fun y => GridExpr.over (fun u => innerQuad vs x y u) (us x)) ys) xs
def fourExchangeChart :
    GridCircuit (X × U × Y × W) (fourOccurrenceExpr xs ys us vs) (fourJointExpr xs ys us vs) :=
  GridCircuit.foreach _ _
    (fun x => GridCircuit.transpose (fun u y => innerQuad vs x y u) ys (us x)) xs

theorem quadCell_eval (x : X) (y : Y) (u : U) :
    GridExpr.eval (S:=S) (Z:=Z) (quadLabels (T:=T) A B) (innerQuad vs x y u) =
      raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B u y :=
  GridExpr.eval_over _ _ _

theorem fourExchangeChart_eval :
    HEq (GridCircuit.eval M (quadLabels (T:=T) A B) (fourExchangeChart xs ys us vs))
      (exchangeInner (T:=T) M A B xs ys us vs) := by
  have comp := GridCircuit.foreach_eval M (quadLabels (T:=T) A B) _ _
    (fun x => GridCircuit.transpose (fun u y => innerQuad vs x y u) ys (us x)) xs
  apply comp.trans
  clear comp
  unfold exchangeInner
  have hadd (x : X) :
      HEq (GridCircuit.eval M (quadLabels (T:=T) A B)
        (GridCircuit.transpose (fun u y => innerQuad vs x y u) ys (us x)))
        (transposeBlock M (raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B) ys (us x)) := by
    have p := GridCircuit.transpose_eval M (quadLabels (T:=T) A B) (fun u y => innerQuad vs x y u) ys (us x)
    have eq : (fun u y => GridExpr.eval (S:=S) (Z:=Z) (quadLabels (T:=T) A B) (innerQuad vs x y u)) =
        raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B := funext fun u => funext fun y => quadCell_eval A B vs x y u
    have c {D E : U → Y → C} (h : D = E) : HEq (transposeBlock M D ys (us x)) (transposeBlock M E ys (us x)) := by
      cases h
      rfl
    exact p.trans (c eq)
  -- Both folds use the same outer occurrence list. Transport each local
  -- arrow together with its actual objects, without identifying addresses.
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [act]
    apply structural_map_heq _ _ _ _ (hadd x) ih
    · repeat rw [GridExpr.eval_over]
      congr 1
      funext u
      rw [GridExpr.eval_over]
      congr 1
      funext y
      exact quadCell_eval A B vs x y u
    · repeat rw [GridExpr.eval_over]
      congr 1
      funext y
      rw [GridExpr.eval_over]
      congr 1
      funext u
      exact quadCell_eval A B vs x y u
    · congr 1
      funext x
      repeat rw [GridExpr.eval_over]
      congr 1
      funext u
      rw [GridExpr.eval_over]
      congr 1
      funext y
      exact quadCell_eval A B vs x y u
    · congr 1
      funext x
      repeat rw [GridExpr.eval_over]
      congr 1
      funext y
      rw [GridExpr.eval_over]
      congr 1
      funext u
      exact quadCell_eval A B vs x y u
end Chart

section ChartObjects
theorem occurrence_expr_obj :
    GridExpr.eval (S:=S) (Z:=Z) (quadLabels (T:=T) A B) (fourOccurrenceExpr xs ys us vs) =
      fold S Z (fun x => fold S Z
        (fun u => fold S Z (raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B u) ys) (us x)) xs := by
  unfold fourOccurrenceExpr
  rw [GridExpr.eval_over]
  congr 1
  funext x
  rw [GridExpr.eval_over]
  congr 1
  funext u
  rw [GridExpr.eval_over]
  congr 1
  funext y
  exact quadCell_eval A B vs x y u
theorem joint_expr_obj :
    GridExpr.eval (S:=S) (Z:=Z) (quadLabels (T:=T) A B) (fourJointExpr xs ys us vs) =
      fold S Z (fun x => fold S Z
        (fun y => fold S Z (fun u => raggedCell (S:=S) (Z:=Z) (T:=T) (A x) vs B u y) (us x)) ys) xs := by
  unfold fourJointExpr
  rw [GridExpr.eval_over]
  congr 1
  funext x
  rw [GridExpr.eval_over]
  congr 1
  funext y
  rw [GridExpr.eval_over]
  congr 1
  funext u
  exact quadCell_eval A B vs x y u
end ChartObjects
end ContextualComposition.NativeFinitePush.DependentFibre
