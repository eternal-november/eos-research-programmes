module
public import ContextualComposition.ChartDistribution
@[expose] public section

/-! Ragged block interchange without forgetting the row, column, or the
addresses below a block. The transpose is an additive map on actual cells,
independent of how those cells are later decomposed. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
set_option backward.isDefEq.respectTransparency false
universe u v w t
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C}
structure AddCross (S : Bi K) (Z : C) where
  merge : K.Hom (S.obj Z Z) Z
  empty : K.Hom Z (S.obj Z Z)
  middle (a b c d : C) : K.Hom (S.obj (S.obj a b) (S.obj c d)) (S.obj (S.obj a c) (S.obj b d))
  invol (a b c d : C) : K.seq (middle a b c d) (middle a c b d) = K.id _
  natural {a b c d a' b' c' d' : C}
    (p : K.Hom a a') (q : K.Hom b b') (r : K.Hom c c') (s : K.Hom d d') :
    K.seq (S.map (S.map p q) (S.map r s)) (middle a' b' c' d') =
      K.seq (middle a b c d) (S.map (S.map p r) (S.map q s))
variable (M : AddCross S Z)
variable {X : Type w} {Y : Type t}
def zipBlock (A B : Y → C) : (ys : List Y) →
    K.Hom (S.obj (fold S Z A ys) (fold S Z B ys)) (fold S Z (fun y => S.obj (A y) (B y)) ys)
  | [] => M.merge
  | y::ys => K.seq (M.middle (A y) _ (B y) _) (S.map (K.id _) (zipBlock A B ys))
theorem zipBlock_natural {A B D E : Y → C} (p : ∀ y, K.Hom (A y) (D y)) (q : ∀ y, K.Hom (B y) (E y)) (ys : List Y) :
    K.seq (S.map (act S Z p ys) (act S Z q ys)) (zipBlock M D E ys) =
      K.seq (zipBlock M A B ys) (act S Z (fun y => S.map (p y) (q y)) ys) := by
  induction ys with
  | nil =>
    change K.seq (S.map (K.id Z) (K.id Z)) M.merge = K.seq M.merge (K.id Z)
    rw [S.map_id, K.id_seq, K.seq_id]
  | cons y ys ih =>
    simp only [act, fold, zipBlock]
    rw [← K.assoc, M.natural, K.assoc, ← S.map_seq, K.seq_id, ih, ← K.id_seq (S.map (p y) (q y)),
      S.map_seq, K.id_seq, K.assoc]

def zeros : (ys : List Y) → K.Hom Z (fold S Z (fun _ => Z) ys)
  | [] => K.id _
  | _::ys => K.seq M.empty (S.map (K.id Z) (zeros ys))
theorem act_id_grid {A : X → C} (xs : List X) :
    act S Z (fun x => K.id (A x)) xs = K.id (fold S Z A xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [fold, act, ih, S.map_id]
def transposeBlock (A : X → Y → C) (ys : List Y) : (xs : List X) →
    K.Hom (fold S Z (fun x => fold S Z (A x) ys) xs)
      (fold S Z (fun y => fold S Z (fun x => A x y) xs) ys)
  | [] => zeros M ys
  | x::xs => K.seq (S.map (K.id _) (transposeBlock A ys xs)) (zipBlock M (A x) _ ys)
theorem transposeBlock_natural {A B : X → Y → C} (p : ∀ x y, K.Hom (A x y) (B x y))
    (xs : List X) (ys : List Y) :
    K.seq (act S Z (fun x => act S Z (p x) ys) xs) (transposeBlock M B ys xs) =
      K.seq (transposeBlock M A ys xs) (act S Z (fun y => act S Z (fun x => p x y) xs) ys) := by
  induction xs with
  | nil => simp only [act, fold, transposeBlock, act_id_grid, K.id_seq, K.seq_id]
  | cons x xs ih =>
    simp only [act, fold, transposeBlock]
    rw [← K.assoc, ← S.map_seq, K.seq_id, ih, ← K.id_seq (act S Z (p x) ys), S.map_seq, K.assoc,
      zipBlock_natural]
    simp only [K.assoc]

abbrev Lin.plus (F : Lin S Z) (M : AddCross S Z) (G : Lin S Z) : Lin S Z where
  obj x := S.obj (F.obj x) (G.obj x)
  map p := S.map (F.map p) (G.map p)
  id _ := by rw [F.id, G.id, S.map_id]
  seq p q := by rw [F.seq, G.seq, S.map_seq]
  nil := K.seq M.empty (S.map F.nil G.nil)
  cons a b := K.seq (M.middle _ _ _ _) (S.map (F.cons a b) (G.cons a b))
abbrev Lin.zero (M : AddCross S Z) : Lin S Z where
  obj _ := Z
  map _ := K.id Z
  id _ := rfl
  seq _ _ := (K.id_seq _).symm
  nil := K.id Z
  cons _ _ := M.merge

variable {T : Bi K} (R : Gather S T Z) (L : LeftGather S T Z)
/-- The mixed right/left distributor and absorption squares; their inputs
are only binary sums and zero, as in RigGrid.GridData. -/
structure GridBinary : Prop where
  mergeInv : K.seq M.empty M.merge = K.id Z
  splitInv : K.seq M.merge M.empty = K.id (S.obj Z Z)
  bin (a b : C) : LinSquare ((Lin.left L a).plus M (Lin.left L b)) (Lin.left L (S.obj a b))
    (fun c => R.cons a b c)
  nil : LinSquare (Lin.zero M) (Lin.left L Z) (fun c => R.nil c)

theorem point_collect (F G : Lin S Z) (A : Y → C) (ys : List Y)
    (hi : K.seq M.merge M.empty = K.id (S.obj Z Z)) :
    K.seq (zipBlock M (fun y => F.obj (A y)) (fun y => G.obj (A y)) ys)
      ((F.plus M G).collect A ys) =
    S.map (F.collect A ys) (G.collect A ys) := by
  induction ys with
  | nil =>
    change K.seq M.merge (K.seq M.empty (S.map F.nil G.nil)) = S.map F.nil G.nil
    rw [← K.assoc, hi, K.id_seq]
  | cons y ys ih =>
    simp only [Lin.collect, Lin.plus, zipBlock, fold, K.assoc]
    rw [← K.assoc (S.map (K.id _) (zipBlock _ _ _ _)), ← S.map_seq, K.id_seq, ih]
    have h := M.natural (K.id (F.obj (A y))) (F.collect A ys) (K.id (G.obj (A y))) (G.collect A ys)
    rw [← K.assoc (S.map (K.id _) _), ← S.map_id]
    simp only [K.assoc]
    rw [← K.assoc (M.middle (F.obj (A y)) _ (G.obj (A y)) _), ← h, K.assoc, ← K.assoc (M.middle (F.obj (A y)) _ (G.obj (A y)) _), M.invol, K.id_seq, ← S.map_seq]
variable (N : GridBinary M R L)
include N in
theorem zero_collect (A : Y → C) (ys : List Y) :
    K.seq (zeros M ys) ((Lin.zero M).collect A ys) = K.id Z := by
  induction ys with
  | nil => exact K.id_seq _
  | cons y ys ih =>
    simp only [zeros, Lin.collect, Lin.zero]
    rw [K.assoc, ← K.assoc (S.map (K.id Z) (zeros M ys)), ← S.map_seq, K.id_seq, ih, S.map_id, K.id_seq]
    exact N.mergeInv
variable (V : X → C) (W : Y → C) (xs : List X) (ys : List Y)
def tally (a : C) := (Lin.left L a).collect W ys
def colGather :=
  K.seq (act S Z (fun y => gather R V (W y) xs) ys) (tally L W ys (fold S Z V xs))
def rowGather :=
  K.seq (act S Z (fun x => tally L W ys (V x)) xs) (gather R V (fold S Z W ys) xs)
include N in
theorem row_col_gather :
    K.seq (transposeBlock M (fun x y => T.obj (V x) (W y)) ys xs)
      (colGather R L V W xs ys) = rowGather R L V W xs ys := by
  induction xs with
  | nil =>
    unfold colGather rowGather tally
    simp only [transposeBlock, act, gather, fold, K.id_seq]
    rw [← (N.nil.collect W ys), ← K.assoc, zero_collect M R L N W ys, K.id_seq]
  | cons x xs ih =>
    unfold colGather rowGather tally at ih ⊢
    simp only [transposeBlock, act, gather, fold]
    simp only [K.assoc]
    rw [← act_seq, K.assoc (act S Z _ ys), ← (N.bin (V x) (fold S Z V xs)).collect W ys]
    rw [← K.assoc (zipBlock _ _ _ _), ← zipBlock_natural]
    simp only [K.assoc]
    rw [← K.assoc (zipBlock _ _ _ _), point_collect M (Lin.left L (V x)) (Lin.left L (fold S Z V xs)) W ys N.splitInv]
    simp only [act_id_grid, ← K.assoc, ← S.map_seq, K.id_seq, K.seq_id]
    rw [K.assoc (transposeBlock _ _ _ _), ih]

variable {B : Type t} (branches : Y → List B) (A : Y → B → C)
/-- A family of ragged right-branch charts; entries are whole branch
sums. No premise that all branches have the same cardinality. -/
def raggedCell (x : X) (y : Y) := fold S Z (fun b => T.obj (V x) (A y b)) (branches y)
def raggedGather (x : X) (y : Y) := (Lin.left L (V x)).collect (A y) (branches y)
def raggedRowGather :=
  K.seq (act S Z (fun x => act S Z (raggedGather L V branches A x) ys) xs)
    (rowGather R L V (fun y => fold S Z (A y) (branches y)) xs ys)
def raggedColGather :=
  K.seq (act S Z (fun y =>
      rowGather R L V (A y) xs (branches y)) ys)
    ((Lin.left L (fold S Z V xs)).collect (fun y => fold S Z (A y) (branches y)) ys)

include N in
/-- Ragged two-axis interchange. The left order is x,y,b(y); the right
order is y,x,b(y). Each branch list can be empty. Independent definitions
of the two schedules gather the inner list at different points. -/
theorem ragged_interchange :
    K.seq (transposeBlock M (raggedCell V branches A) ys xs)
      (raggedColGather R L V xs ys branches A) =
    raggedRowGather R L V xs ys branches A := by
  let B' (y : Y) := fold S Z (A y) (branches y)
  let p (x : X) (y : Y) := raggedGather L V branches A x y
  have square := transposeBlock_natural M p xs ys
  change K.seq (act S Z (fun x => act S Z (p x) ys) xs) (transposeBlock M (fun x y => T.obj (V x) (B' y)) ys xs) = K.seq (transposeBlock M (raggedCell V branches A) ys xs) (act S Z (fun y => act S Z (fun x => p x y) xs) ys) at square
  have h := row_col_gather M R L N V B' xs ys
  unfold raggedRowGather raggedColGather rowGather
  rw [← act_seq, ← K.assoc]
  change K.seq (K.seq (transposeBlock M (raggedCell V branches A) ys xs)
    (K.seq (act S Z (fun y => act S Z (fun x => p x y) xs) ys)
      (act S Z (fun y => gather R V (B' y) xs) ys))) _ = _
  rw [← K.assoc (transposeBlock _ _ _ _), ← square, K.assoc, K.assoc]
  change K.seq (act S Z (fun x => act S Z (p x) ys) xs)
    (K.seq (transposeBlock M _ ys xs) (colGather R L V B' xs ys)) = _
  rw [h]
  rfl

variable (i₁ : K.seq M.empty M.merge = K.id Z) (i₂ : K.seq M.merge M.empty = K.id (S.obj Z Z))
def zipBlockInv (A B : Y → C) : (ys : List Y) → Inv (zipBlock M A B ys)
  | [] => ⟨M.empty,i₂,i₁⟩
  | y::ys =>
    let a := A y
    let b := fold S Z A ys
    let c := B y
    let d := fold S Z B ys
    let m : Inv (M.middle a b c d) := ⟨M.middle a c b d,M.invol a b c d,M.invol a c b d⟩
    m.comp ((Inv.ident _).tensor (zipBlockInv A B ys))
def zerosInv : (ys : List Y) → Inv (zeros M ys)
  | [] => Inv.ident _
  | _::ys => (Inv.mk M.merge i₁ i₂).comp ((Inv.ident _).tensor (zerosInv ys))
def transposeBlockInv (A : X → Y → C) (ys : List Y) : (xs : List X) → Inv (transposeBlock M A ys xs)
  | [] => zerosInv M i₁ i₂ ys
  | x::xs =>
    ((Inv.ident _).tensor (transposeBlockInv A ys xs)).comp
      (zipBlockInv M i₁ i₂ (A x) (fun y => fold S Z (fun x => A x y) xs) ys)
include N in
/-- Postcompose each schedule with an arbitrary whole-block arrow. The
comparison is an isomorphism and reflects equality of any competing arrows
out of the column, so it is usable in opaque-aggregate composites. -/
theorem ragged_native_post {q : C}
    (β : K.Hom (T.obj (fold S Z V xs) (fold S Z (fun y => fold S Z (A y) (branches y)) ys)) q) :
    K.seq (transposeBlock M (raggedCell V branches A) ys xs)
      (K.seq (raggedColGather R L V xs ys branches A) β) =
    K.seq (raggedRowGather R L V xs ys branches A) β := by
  rw [← K.assoc, ragged_interchange M R L N]
end ContextualComposition.NativeFinitePush.DependentFibre
