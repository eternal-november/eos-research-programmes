module
public import ContextualComposition.RaggedGrid
@[expose] public section

/-! Structural additive circuits used for the transport. Leaves are actual
blocks. A syntactic zero is represented separately from a leaf whose
coefficient object happens to be zero. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
set_option backward.isDefEq.respectTransparency false
universe u v w x y
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C}
inductive GridExpr (I : Type w)
  | zero
  | leaf (i : I)
  | bin (a b : GridExpr I)
namespace GridExpr
variable {I : Type w}
def eval (A : I → C) : GridExpr I → C
  | .zero => Z
  | .leaf i => A i
  | .bin a b => S.obj (eval A a) (eval A b)
def sumList (A : I → GridExpr I) : List I → GridExpr I
  | [] => .zero
  | x::xs => .bin (A x) (sumList A xs)
def gatherE (F : Lin S Z) (A : I → C) : (e : GridExpr I) →
    K.Hom (eval (S:=S) (Z:=Z) (fun i => F.obj (A i)) e) (F.obj (eval (S:=S) (Z:=Z) A e))
  | .zero => F.nil
  | .leaf i => K.id (F.obj (A i))
  | .bin a b => K.seq (S.map (gatherE F A a) (gatherE F A b)) (F.cons _ _)
end GridExpr
variable {I : Type w} (M : AddCross S Z)
inductive GridCircuit (I : Type w) : GridExpr I → GridExpr I → Type w
  | ident (e) : GridCircuit I e e
  | seq {a b c} : GridCircuit I a b → GridCircuit I b c → GridCircuit I a c
  | bin {a b c d} : GridCircuit I a c → GridCircuit I b d →
      GridCircuit I (.bin a b) (.bin c d)
  | dupZero : GridCircuit I .zero (.bin .zero .zero)
  | mergeZero : GridCircuit I (.bin .zero .zero) .zero
  | middle (a b c d) : GridCircuit I (.bin (.bin a b) (.bin c d)) (.bin (.bin a c) (.bin b d))
namespace GridCircuit
variable (A : I → C)
def eval {a b} : GridCircuit I a b →
    K.Hom (GridExpr.eval (S:=S) (Z:=Z) A a) (GridExpr.eval (S:=S) (Z:=Z) A b)
  | .ident _ => K.id _
  | .seq p q => K.seq (eval p) (eval q)
  | .bin p q => S.map (eval p) (eval q)
  | .dupZero => M.empty
  | .mergeZero => M.merge
  | .middle _ _ _ _ => M.middle _ _ _ _
end GridCircuit
variable (F : Lin S Z)
structure LinCross : Prop where
  dup : K.seq M.empty (K.seq (S.map F.nil F.nil) (F.cons Z Z)) = K.seq F.nil (F.map M.empty)
  merge : K.seq M.merge F.nil = K.seq (K.seq (S.map F.nil F.nil) (F.cons Z Z)) (F.map M.merge)
  middle (a b c d : C) :
    K.seq (M.middle (F.obj a) (F.obj b) (F.obj c) (F.obj d))
      (K.seq (S.map (F.cons a c) (F.cons b d)) (F.cons (S.obj a c) (S.obj b d))) =
    K.seq (K.seq (S.map (F.cons a b) (F.cons c d)) (F.cons (S.obj a b) (S.obj c d)))
      (F.map (M.middle a b c d))

variable (N : LinNatural F) (P : LinCross M F)
include N P in
theorem GridCircuit.gather_commutes (A : I → C) {a b} (p : GridCircuit I a b) :
    K.seq (GridCircuit.eval M (fun i => F.obj (A i)) p) (GridExpr.gatherE F A b) =
    K.seq (GridExpr.gatherE F A a) (F.map (GridCircuit.eval M A p)) := by
  induction p with
  | ident => simp only [GridCircuit.eval, F.id, K.seq_id, K.id_seq]
  | seq p q hp hq =>
    simp only [GridCircuit.eval, F.seq, K.assoc]
    rw [hq, ← K.assoc, hp, K.assoc]
  | bin p q hp hq =>
    simp only [GridCircuit.eval, GridExpr.gatherE]
    rw [← K.assoc, ← S.map_seq, hp, hq, S.map_seq, K.assoc, N.bin, ← K.assoc]
  | dupZero => exact P.dup
  | mergeZero => exact P.merge
  | middle a b c d =>
    simp only [GridCircuit.eval, GridExpr.gatherE, GridExpr.eval]
    -- The four subtrees gather independently. Move those four actual maps
    -- through the additive middle before applying the local binary diagram.
    simp only [S.map_seq, K.assoc]
    rw [← K.assoc (M.middle _ _ _ _), ← M.natural, K.assoc]
    rw [← K.assoc (S.map (S.map _ _) (S.map _ _)) (M.middle _ _ _ _)]
    have h := congrArg (K.seq (S.map (S.map (GridExpr.gatherE F A a) (GridExpr.gatherE F A b)) (S.map (GridExpr.gatherE F A c) (GridExpr.gatherE F A d)))) (P.middle (GridExpr.eval A a) (GridExpr.eval A b) (GridExpr.eval A c) (GridExpr.eval A d))
    simpa only [K.assoc] using h

namespace GridExpr
variable {X : Type x}
def over (A : X → GridExpr I) : List X → GridExpr I
  | [] => .zero
  | x::xs => .bin (A x) (over A xs)
theorem eval_over (V : I → C) (A : X → GridExpr I) (xs : List X) :
    eval (S:=S) (Z:=Z) V (over A xs) = fold S Z (fun x => eval (S:=S) (Z:=Z) V (A x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [over, eval, fold, ih]
end GridExpr
namespace GridCircuit
open GridExpr
variable {X : Type x} {Y : Type y}
def zip (A B : Y → GridExpr I) : (ys : List Y) →
    GridCircuit I (.bin (over A ys) (over B ys)) (over (fun y => .bin (A y) (B y)) ys)
  | [] => .mergeZero
  | y::ys => .seq (.middle (A y) (over A ys) (B y) (over B ys)) (.bin (.ident _) (zip A B ys))
def emptyRows : (ys : List Y) → GridCircuit I .zero (over (fun _ => .zero) ys)
  | [] => .ident _
  | _::ys => .seq .dupZero (.bin (.ident _) (emptyRows ys))
def transpose (A : X → Y → GridExpr I) (ys : List Y) : (xs : List X) →
    GridCircuit I (over (fun x => over (A x) ys) xs) (over (fun y => over (fun x => A x y) xs) ys)
  | [] => emptyRows ys
  | x::xs => .seq (.bin (.ident _) (transpose A ys xs)) (zip (A x) (fun y => over (fun x => A x y) xs) ys)
def raggedTranspose {B : Type w} (branches : Y → List B) (A : X → Y → B → GridExpr I)
    (xs : List X) (ys : List Y) :=
  transpose (fun x y => over (A x y) (branches y)) ys xs

include N P in
/-- The ragged axis exchange survives a surrounding tensor functor, with its
independently computed gathers at the two source chart orders. It may be
iterated through several contexts; the conditions are local generator laws. -/
theorem ragged_context {B : Type w} (branches : Y → List B) (A : X → Y → B → GridExpr I)
    (xs : List X) (ys : List Y) (V : I → C) :
    K.seq (eval M (fun i => F.obj (V i)) (raggedTranspose branches A xs ys))
      (gatherE F V (over (fun y => over (fun x => over (A x y) (branches y)) xs) ys)) =
    K.seq (gatherE F V (over (fun x => over (fun y => over (A x y) (branches y)) ys) xs))
      (F.map (eval M V (raggedTranspose branches A xs ys))) :=
  gather_commutes M F N P V _
end GridCircuit

section Decode
variable {a b c a' b' c' : C}
theorem structural_seq_heq (ea : a = a') (eb : b = b') (ec : c = c')
    {f : K.Hom a b} {g : K.Hom b c} {f' : K.Hom a' b'} {g' : K.Hom b' c'}
    (h : HEq f f') (j : HEq g g') : HEq (K.seq f g) (K.seq f' g') := by
  subst a'; subst b'; subst c'; cases h; cases j; rfl
theorem structural_map_heq {d d' : C} (ea : a = a') (eb : b = b') (ec : c = c') (ed : d = d')
    {f : K.Hom a b} {g : K.Hom c d} {f' : K.Hom a' b'} {g' : K.Hom c' d'}
    (h : HEq f f') (j : HEq g g') : HEq (S.map f g) (S.map f' g') := by
  subst a'; subst b'; subst c'; subst d'; cases h; cases j; rfl
theorem structural_id_heq (ea : a = a') : HEq (K.id a) (K.id a') := by subst a';rfl
end Decode

namespace GridCircuit
open GridExpr
variable {X : Type x} {Y : Type y} (A : I → C)
theorem zip_eval (P Q : Y → GridExpr I) (ys : List Y) :
    HEq (eval M A (zip P Q ys))
      (zipBlock M (fun y => GridExpr.eval (S:=S) (Z:=Z) A (P y))
        (fun y => GridExpr.eval (S:=S) (Z:=Z) A (Q y)) ys) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [zip, eval, zipBlock, GridExpr.eval, GridExpr.over]
    refine structural_seq_heq (by rw [GridExpr.eval_over, GridExpr.eval_over]; rfl)
      (by rw [GridExpr.eval_over, GridExpr.eval_over])
      (by rw [GridExpr.eval_over]; rfl) ?_ ?_
    · rw [GridExpr.eval_over, GridExpr.eval_over]
    · exact structural_map_heq rfl rfl (by rw [GridExpr.eval_over, GridExpr.eval_over]) (by rw [GridExpr.eval_over]; rfl) HEq.rfl ih
theorem emptyRows_eval (ys : List Y) :
    HEq (eval M A (emptyRows ys)) (zeros M ys) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [emptyRows, eval, zeros]
    refine structural_seq_heq rfl rfl ?_ HEq.rfl ?_
    · rw [GridExpr.eval_over]; rfl
    · exact structural_map_heq rfl rfl rfl (GridExpr.eval_over _ _ _) HEq.rfl ih
theorem transpose_eval (P : X → Y → GridExpr I) (ys : List Y) (xs : List X) :
    HEq (eval M A (transpose P ys xs))
      (transposeBlock M (fun x y => GridExpr.eval (S:=S) (Z:=Z) A (P x y)) ys xs) := by
  induction xs with
  | nil => exact emptyRows_eval M A ys
  | cons x xs ih =>
    simp only [transpose, eval, transposeBlock]
    have hr : ∀ zs : List X, GridExpr.eval (S:=S) (Z:=Z) A (over (fun x => over (P x) ys) zs) =
        fold S Z (fun x => fold S Z (fun y => GridExpr.eval (S:=S) (Z:=Z) A (P x y)) ys) zs := by
      intro zs
      rw [GridExpr.eval_over]
      congr 1
      funext x
      exact GridExpr.eval_over _ _ _
    have hc : ∀ zs : List X, GridExpr.eval (S:=S) (Z:=Z) A (over (fun y => over (fun x => P x y) zs) ys) =
        fold S Z (fun y => fold S Z (fun x => GridExpr.eval (S:=S) (Z:=Z) A (P x y)) zs) ys := by
      intro zs
      rw [GridExpr.eval_over]
      congr 1
      funext y
      exact GridExpr.eval_over _ _ _
    refine structural_seq_heq (hr (x::xs)) ?_ (hc (x::xs)) ?_ ?_
    · simp only [GridExpr.eval, GridExpr.eval_over, hc]
    · exact structural_map_heq (GridExpr.eval_over _ _ _) (GridExpr.eval_over _ _ _) (hr xs) (hc xs)
        (structural_id_heq (GridExpr.eval_over _ _ _)) ih
    · have h := zip_eval M A (P x) (fun y => over (fun x => P x y) xs) ys
      have eo : (fun y => GridExpr.eval (S:=S) (Z:=Z) A (over (fun x => P x y) xs)) =
          (fun y => fold S Z (fun x => GridExpr.eval (S:=S) (Z:=Z) A (P x y)) xs) :=
        funext fun _ => GridExpr.eval_over _ _ _
      have cong {F G : Y → C} (e : F = G) :
          HEq (zipBlock M (fun y => GridExpr.eval (S:=S) (Z:=Z) A (P x y)) F ys)
            (zipBlock M (fun y => GridExpr.eval (S:=S) (Z:=Z) A (P x y)) G ys) := by cases e; rfl
      exact h.trans (cong eo)
end GridCircuit


section Composites
open GridExpr GridCircuit
variable {X Y B : Type w} {T : Bi K}
variable (R : Gather S T Z) (L : LeftGather S T Z)
variable (V : X → C) (A : Y → B → C) (branches : Y → List B) (xs : List X) (ys : List Y)
abbrev Triple (X Y B : Type w) := X × Y × B
def labels (p : Triple X Y B) := T.obj (V p.1) (A p.2.1 p.2.2)
def branchTree (x : X) (y : Y) := over (fun b => leaf (x,y,b)) (branches y)
def rowTree := over (fun x => over (branchTree branches x) ys) xs
def colTree := over (fun y => over (fun x => branchTree branches x y) xs) ys
def chartC : GridCircuit (Triple X Y B) (rowTree (B:=B) branches xs ys) (colTree branches xs ys) :=
  transpose (branchTree branches) ys xs
theorem eval_leaf_branch (x : X) (y : Y) :
    GridExpr.eval (S:=S) (Z:=Z) (labels (T:=T) V A) (branchTree branches x y) =
      raggedCell (T:=T) (S:=S) (Z:=Z) V branches A x y :=
  eval_over _ _ _
theorem eval_row_tree :
    GridExpr.eval (S:=S) (Z:=Z) (labels (T:=T) V A) (rowTree branches xs ys) =
      fold S Z (fun x => fold S Z (raggedCell (T:=T) (S:=S) (Z:=Z) V branches A x) ys) xs := by
  unfold rowTree
  rw [eval_over]
  congr 1
  funext x
  rw [eval_over]
  congr 1
  funext y
  exact eval_leaf_branch (T:=T) V A branches x y
theorem eval_col_tree :
    GridExpr.eval (S:=S) (Z:=Z) (labels (T:=T) V A) (colTree branches xs ys) =
      fold S Z (fun y => fold S Z (fun x => raggedCell (T:=T) (S:=S) (Z:=Z) V branches A x y) xs) ys := by
  unfold colTree
  rw [eval_over]
  congr 1
  funext y
  rw [eval_over]
  congr 1
  funext x
  exact eval_leaf_branch (T:=T) V A branches x y
theorem chart_eval :
    HEq (GridCircuit.eval M (labels (T:=T) V A) (chartC branches xs ys))
      (transposeBlock M (raggedCell (T:=T) (S:=S) (Z:=Z) V branches A) ys xs) := by
  have e : (fun x y => GridExpr.eval (S:=S) (Z:=Z) (labels (T:=T) V A) (branchTree branches x y)) =
    raggedCell (T:=T) (S:=S) (Z:=Z) V branches A :=
    funext fun x => funext fun y => eval_leaf_branch (T:=T) V A branches x y
  have cong {D E : X → Y → C} (h : D = E) :
      HEq (transposeBlock M D ys xs) (transposeBlock M E ys xs) := by cases h;rfl
  exact (transpose_eval M (labels (T:=T) V A) (branchTree branches) ys xs).trans (cong e)

def transportSource {a b d : C} (p : a = b) (h : K.Hom b d) : K.Hom a d :=
  p.symm ▸ h
theorem transport_paste {a b a' b' d : C} (p : a = a') (q : b = b')
    {f : K.Hom a b} {f' : K.Hom a' b'} (hh : HEq f f') (g : K.Hom b' d) :
    K.seq f (transportSource q g) = transportSource p (K.seq f' g) := by
  cases p; cases q; cases hh; rfl
variable (D : GridBinary M R L)

include N P D in
/-- Compare contextualized semantic maps, not only the expression evaluator:
transport the maps proved in the ragged grid theorem to their respective
typed expression endpoints, then apply the real outside functor. -/
theorem actual_ragged_context {q : C}
    (β : K.Hom (T.obj (fold S Z V xs) (fold S Z (fun y => fold S Z (A y) (branches y)) ys)) q) :
    K.seq (GridCircuit.eval M (fun i => F.obj (labels (T:=T) V A i)) (chartC branches xs ys))
      (K.seq (gatherE F (labels (T:=T) V A) (colTree branches xs ys))
        (F.map (transportSource (eval_col_tree (T:=T) V A branches xs ys)
          (K.seq (raggedColGather R L V xs ys branches A) β)))) =
    K.seq (gatherE F (labels (T:=T) V A) (rowTree branches xs ys))
      (F.map (transportSource (eval_row_tree (T:=T) V A branches xs ys)
        (K.seq (raggedRowGather R L V xs ys branches A) β))) := by
  rw [← K.assoc, GridCircuit.gather_commutes M F N P, K.assoc, ← F.seq,
    transport_paste (eval_row_tree (T:=T) V A branches xs ys) (eval_col_tree (T:=T) V A branches xs ys)
      (chart_eval (T:=T) M V A branches xs ys), ragged_native_post M R L D]
end Composites

namespace GridExpr
variable {I : Type w}
def leaves : GridExpr I → List I
  | .zero => []
  | .leaf i => [i]
  | .bin a b => a.leaves ++ b.leaves
end GridExpr
namespace GridCircuit
theorem leaves_perm {a b} (p : GridCircuit I a b) : a.leaves.Perm b.leaves := by
  induction p with
  | ident => exact List.Perm.refl _
  | seq p q hp hq => exact hp.trans hq
  | bin p q hp hq => exact hp.append hq
  | dupZero | mergeZero => exact .nil
  | middle a b c d =>
    simp only [GridExpr.leaves, List.append_assoc]
    apply List.Perm.append_left
    simpa only [List.append_assoc] using (List.perm_append_comm (l₁:=b.leaves) (l₂:=c.leaves)).append_right d.leaves
end GridCircuit

variable {H : AddStruct S Z} (J : AddInvertible H)
/-- The actual chosen right unitor removes the trailing fold zero at a
single leaf; a real zero-labelled leaf remains present. -/
structure FoldLeafUnit where
  hom (a : C) : K.Hom (S.obj a Z) a
  inv (a : C) : Inv (hom a)
variable (E : FoldLeafUnit (S:=S) (Z:=Z)) (A : I → C)
def GridExpr.fromFlat : (e : GridExpr I) → K.Hom (fold S Z A e.leaves) (GridExpr.eval (S:=S) (Z:=Z) A e)
  | .zero => K.id Z
  | .leaf i => E.hom (A i)
  | .bin a b => K.seq (join H A a.leaves b.leaves) (S.map (fromFlat a) (fromFlat b))
def GridExpr.fromFlatInv : (e : GridExpr I) → Inv (GridExpr.fromFlat (H:=H) E A e)
  | .zero => Inv.ident _
  | .leaf i => E.inv (A i)
  | .bin a b => (joinInv J A a.leaves b.leaves).comp ((fromFlatInv a).tensor (fromFlatInv b))

/-- A flat coefficient fibre whose raw address list is a specified reorder
of the leaves. This arrow is independent of the arrows subsequently applied
to its branch coefficients. -/
def GridExpr.chartFrom {is : List I} (e : GridExpr I) (r : AddressOrder I is e.leaves) :=
  K.seq (r.mapSum H A) (GridExpr.fromFlat (H:=H) E A e)
def GridExpr.chartFromInv {is : List I} (e : GridExpr I) (r : AddressOrder I is e.leaves) :
    Inv (GridExpr.chartFrom (H:=H) E A e r) :=
  (r.mapSumInv J).comp (GridExpr.fromFlatInv J E A e)

section FlatContext
variable {X Y B : Type w} {T : Bi K} {H : AddStruct S Z}
variable (R : Gather S T Z) (L : LeftGather S T Z) (D : GridBinary M R L)
variable (V : X → C) (A : Y → B → C) (bs : Y → List B) (xs : List X) (ys : List Y)
variable (E : FoldLeafUnit (S:=S) (Z:=Z))
theorem GridExpr.mem_over {I V : Type w} (Q : V → GridExpr I) (vs : List V) (i : I) :
    i ∈ (GridExpr.over Q vs).leaves ↔ ∃ v ∈ vs, i ∈ (Q v).leaves := by
  induction vs with
  | nil => simp [GridExpr.over,GridExpr.leaves]
  | cons v vs ih => simp only [GridExpr.over,GridExpr.leaves,List.mem_append,List.mem_cons,ih]; grind
theorem row_mem (p : Triple X Y B) :
    p ∈ (rowTree bs xs ys).leaves ↔ p.1 ∈ xs ∧ p.2.1 ∈ ys ∧ p.2.2 ∈ bs p.2.1 := by
  simp only [rowTree, branchTree, GridExpr.mem_over, GridExpr.leaves, List.mem_singleton]
  constructor
  · rintro ⟨x,hx,y,hy,b,hb,h⟩
    cases h
    exact ⟨hx,hy,hb⟩
  · rintro ⟨hx,hy,hb⟩
    exact ⟨p.1,hx,p.2.1,hy,p.2.2,hb,rfl⟩
theorem col_mem (p : Triple X Y B) :
    p ∈ (colTree bs xs ys).leaves ↔ p.1 ∈ xs ∧ p.2.1 ∈ ys ∧ p.2.2 ∈ bs p.2.1 :=
  ((GridCircuit.leaves_perm (chartC bs xs ys)).mem_iff).symm.trans (row_mem bs xs ys p)
variable {q : C}
variable (β : K.Hom (T.obj (fold S Z V xs) (fold S Z (fun y => fold S Z (A y) (bs y)) ys)) q)
def flatRowRoute {is : List (Triple X Y B)} (p : AddressOrder (Triple X Y B) is (rowTree bs xs ys).leaves) :=
  K.seq (GridExpr.chartFrom (H:=H) E (fun i => F.obj (labels (T:=T) V A i)) (rowTree bs xs ys) p)
    (K.seq (GridExpr.gatherE F (labels (T:=T) V A) (rowTree bs xs ys))
      (F.map (transportSource (eval_row_tree (T:=T) V A bs xs ys)
        (K.seq (raggedRowGather R L V xs ys bs A) β))))
def flatColumnRoute {is : List (Triple X Y B)} (p : AddressOrder (Triple X Y B) is (rowTree bs xs ys).leaves) :=
  K.seq (K.seq (GridExpr.chartFrom (H:=H) E (fun i => F.obj (labels (T:=T) V A i)) (rowTree bs xs ys) p)
      (GridCircuit.eval M (fun i => F.obj (labels (T:=T) V A i)) (chartC bs xs ys)))
    (K.seq (GridExpr.gatherE F (labels (T:=T) V A) (colTree bs xs ys))
      (F.map (transportSource (eval_col_tree (T:=T) V A bs xs ys)
        (K.seq (raggedColGather R L V xs ys bs A) β))))
include N P D in
theorem actual_ragged_flat {is : List (Triple X Y B)}
    (p : AddressOrder (Triple X Y B) is (rowTree bs xs ys).leaves) :
    flatRowRoute (H:=H) F R L V A bs xs ys E β p =
    flatColumnRoute (H:=H) M F R L V A bs xs ys E β p := by
  unfold flatRowRoute flatColumnRoute
  rw [K.assoc, actual_ragged_context M F N P R L V A bs xs ys D]
end FlatContext

namespace GridExpr
variable {A B : I → C}
def actE (p : ∀ i, K.Hom (A i) (B i)) : (e : GridExpr I) →
    K.Hom (eval (S:=S) (Z:=Z) A e) (eval (S:=S) (Z:=Z) B e)
  | .zero => K.id Z
  | .leaf i => p i
  | .bin a b => S.map (actE p a) (actE p b)
end GridExpr
namespace GridCircuit
theorem leaf_naturality {A B : I → C} (p : ∀ i, K.Hom (A i) (B i)) {e f : GridExpr I}
    (t : GridCircuit I e f) :
    K.seq (GridExpr.actE p e) (eval M B t) =
      K.seq (eval M A t) (GridExpr.actE p f) := by
  induction t with
  | ident => simp only [eval, K.id_seq, K.seq_id]
  | seq t u ht hu =>
    simp only [eval, ← K.assoc, ht]
    rw [K.assoc, hu, ← K.assoc]
  | bin t u ht hu =>
    simp only [GridExpr.actE, eval, ← S.map_seq, ht, hu]
  | dupZero => simp only [GridExpr.actE, GridExpr.eval, eval, S.map_id, K.id_seq, K.seq_id]
  | mergeZero => simp only [GridExpr.actE, GridExpr.eval, eval, S.map_id, K.id_seq, K.seq_id]
  | middle a b c d =>
    exact M.natural (GridExpr.actE p a) (GridExpr.actE p b) (GridExpr.actE p c) (GridExpr.actE p d)
end GridCircuit

section RawEnumeration
variable {X Y B : Type w}
theorem GridExpr.nodup_over {I V : Type w} (Q : V → GridExpr I) (vs : List V)
    (nd : vs.Nodup) (localNd : ∀ x ∈ vs, (Q x).leaves.Nodup)
    (disjoint : ∀ x ∈ vs, ∀ y ∈ vs, x ≠ y → ∀ i ∈ (Q x).leaves, i ∉ (Q y).leaves) :
    (GridExpr.over Q vs).leaves.Nodup := by
  induction vs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rw [List.nodup_cons] at nd
    change List.Nodup ((Q x).leaves ++ (GridExpr.over Q xs).leaves)
    rw [List.Nodup, List.pairwise_append]
    refine ⟨localNd x (by simp), ih nd.2 (fun i hi => localNd i (by simp [hi]))
      (fun i hi j hj => disjoint i (by simp [hi]) j (by simp [hj])), ?_⟩
    intro a ha b hb e
    subst b
    obtain ⟨y,hy,h⟩ := (GridExpr.mem_over Q xs a).mp hb
    exact (disjoint x (by simp) y (by simp [hy]) (fun eq => nd.1 (eq ▸ hy)) a ha) h
theorem row_nodup (bs : Y → List B) (xs : List X) (ys : List Y)
    (nx : xs.Nodup) (ny : ys.Nodup) (nb : ∀ y ∈ ys, (bs y).Nodup) :
    (rowTree bs xs ys).leaves.Nodup := by
  unfold rowTree
  apply GridExpr.nodup_over _ _ nx
  · intro x _
    apply GridExpr.nodup_over _ _ ny
    · intro y hy
      apply GridExpr.nodup_over _ _ (nb y hy)
      · simp [GridExpr.leaves]
      · intro i _ j _ ne q h
        simp only [GridExpr.leaves, List.mem_singleton] at h ⊢
        subst q
        intro e
        exact ne (congrArg (fun p : Triple X Y B => p.2.2) e)
    · intro y _ z _ ne q h
      simp only [branchTree, GridExpr.mem_over, GridExpr.leaves, List.mem_singleton] at h ⊢
      obtain ⟨b,_,hb⟩ := h
      intro ⟨c,_,hc⟩
      exact ne (congrArg (fun p : Triple X Y B => p.2.1) (hb.symm.trans hc))
  · intro x _ z _ ne q h
    simp only [branchTree, GridExpr.mem_over, GridExpr.leaves, List.mem_singleton] at h ⊢
    obtain ⟨y,_,b,_,hb⟩ := h
    intro ⟨w,_,c,_,hc⟩
    exact ne (congrArg (fun p : Triple X Y B => p.1) (hb.symm.trans hc))

/-- The source and both chart orders can be chosen independently at the
extent of raw addresses. Equality of objects or of coefficient labels is
not a premise of the witness. -/
theorem entryOrders [DecidableEq (Triple X Y B)] (bs : Y → List B) (xs : List X) (ys : List Y)
    (nx : xs.Nodup) (ny : ys.Nodup) (nb : ∀ y ∈ ys, (bs y).Nodup)
    (is : List (Triple X Y B)) (ni : is.Nodup)
    (fibre : ∀ p, p ∈ is ↔ p.1 ∈ xs ∧ p.2.1 ∈ ys ∧ p.2.2 ∈ bs p.2.1) :
    Nonempty (AddressOrder (Triple X Y B) is (rowTree bs xs ys).leaves) ∧
      Nonempty (AddressOrder (Triple X Y B) is (colTree bs xs ys).leaves) := by
  have e : is.Perm (rowTree bs xs ys).leaves := by
    rw [List.perm_iff_count]
    intro p
    rw [ni.count, (row_nodup bs xs ys nx ny nb).count]
    have h := (fibre p).trans (row_mem bs xs ys p).symm
    by_cases hp : p ∈ is
    · simp [hp, h.mp hp]
    · have hn : p ∉ (rowTree bs xs ys).leaves := fun z => hp (h.mpr z)
      simp [hp, hn]
  exact ⟨AddressOrder.ofPerm e, AddressOrder.ofPerm (e.trans (GridCircuit.leaves_perm (chartC bs xs ys)))⟩
end RawEnumeration
end ContextualComposition.NativeFinitePush.DependentFibre
