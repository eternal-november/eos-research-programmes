module
public import ContextualComposition.ContextualRaggedGrid
public import ContextualComposition.ReverseFlatCoherence
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
universe u w
variable {I : Type w}
abbrev sumCross : AddCross sum.{u} PEmpty where
  merge := Sum.inr
  empty := Sum.elim PEmpty.elim id
  middle _ _ _ _ := fun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr (.inl c)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr d) => .inr (.inr d)
  invol _ _ _ _ := by funext x; rcases x with (a | b) | (c | d) <;> rfl
  natural _ _ _ _ := by funext x; rcases x with (a | b) | (c | d) <;> rfl
def foldLeafUnit : FoldLeafUnit (S:=sum.{u}) (Z:=PEmpty) where
  hom _ := Sum.inl
  inv _ := ⟨Sum.elim id PEmpty.elim,by funext x; cases x with | inl => rfl | inr v => exact v.elim,rfl⟩

variable (A : I → Type u)
def untag : (e : GridExpr I) → GridExpr.eval (S:=sum) (Z:=PEmpty) A e → Sigma A
  | .zero, token => token.elim
  | .leaf i, token => ⟨i,token⟩
  | .bin p _, .inl token => untag p token
  | .bin _ q, .inr token => untag q token
theorem circuit_tags {e f : GridExpr I} (p : GridCircuit I e f) (v : GridExpr.eval (S:=sum) (Z:=PEmpty) A f) :
    untag A e (GridCircuit.eval sumCross A p v) = untag A f v := by
  induction p with
  | ident => rfl
  | seq p q hp hq => exact (hp _).trans (hq v)
  | bin p q hp hq => cases v with | inl x => exact hp x | inr y => exact hq y
  | mergeZero => exact v.elim
  | dupZero => cases v <;> exact ‹PEmpty›.elim
  | middle => rcases v with (a | b) | (c | d) <;> rfl

theorem lookup_join (xs ys : List I) (v : sum.obj (fold sum PEmpty A xs) (fold sum PEmpty A ys)) :
    lookup (xs ++ ys) (join addStruct A xs ys v) =
      Sum.elim (lookup xs) (lookup ys) v := by
  induction xs with
  | nil => cases v with | inl x => exact x.elim | inr y => rfl
  | cons x xs ih =>
    rcases v with (a | b) | c
    · rfl
    · exact ih (.inl b)
    · exact ih (.inr c)

theorem flat_tags (e : GridExpr I) (v : GridExpr.eval (S:=sum) (Z:=PEmpty) A e) :
    lookup e.leaves (GridExpr.fromFlat (H:=addStruct) foldLeafUnit A e v) = untag A e v := by
  induction e with
  | zero => exact v.elim
  | leaf => rfl
  | bin a b ha hb =>
    cases v with
    | inl v => exact (lookup_join A a.leaves b.leaves (.inl _)).trans (ha v)
    | inr v => exact (lookup_join A a.leaves b.leaves (.inr _)).trans (hb v)
theorem chart_tags {is : List I} (e : GridExpr I) (p : AddressOrder I is e.leaves)
    (v : GridExpr.eval (S:=sum) (Z:=PEmpty) A e) :
    lookup is (GridExpr.chartFrom (H:=addStruct) foldLeafUnit A e p v) = untag A e v :=
  (lookup_order A p _).trans (flat_tags A e v)
theorem lookup_inj [DecidableEq I] (is : List I) (nd : is.Nodup)
    {a b : fold sum PEmpty A is} (h : lookup is a = lookup is b) : a = b := by
  let decode (z : {z : Sigma A // z.1 ∈ is}) := inject is z.val.1 z.property z.val.2
  have hh : (⟨lookup is a,lookup_mem is a⟩ : {z : Sigma A // z.1 ∈ is}) =
      ⟨lookup is b,lookup_mem is b⟩ := Subtype.ext h
  exact (inject_lookup is nd a).symm.trans ((congrArg decode hh).trans (inject_lookup is nd b))

/-- Both entry charts are constructed independently. After decoding raw
tags, the equation is exact, not merely a permutation of equal coefficients.
Duplicate-free refers to raw addresses, not to coefficient labels. -/
theorem independent_charts [DecidableEq I] {is : List I} (nd : is.Nodup) {e f : GridExpr I}
    (p : AddressOrder I is e.leaves) (q : AddressOrder I is f.leaves) (t : GridCircuit I e f) :
    coeff.seq (GridExpr.chartFrom (H:=addStruct) foldLeafUnit A e p) (GridCircuit.eval sumCross A t) =
      GridExpr.chartFrom (H:=addStruct) foldLeafUnit A f q := by
  funext v
  apply lookup_inj A is nd
  exact (chart_tags A e p _).trans ((circuit_tags A t v).trans (chart_tags A f q v).symm)
theorem gridBinary : GridBinary sumCross.{u} gather left where
  mergeInv := rfl
  splitInv := by funext x; cases x <;> exact ‹PEmpty›.elim
  bin a b := {
    nil := by funext x; exact x.2.elim
    cons := by intro c d; funext ⟨p,q⟩; cases p <;> cases q <;> rfl }
  nil := {
    nil := by funext x; exact x.1.elim
    cons := by intro a b; funext x; exact x.1.elim }
theorem leftCross (a : Type u) : LinCross sumCross (Lin.left left a) where
  dup := by funext x; cases x.2 <;> exact ‹PEmpty›.elim
  merge := by funext x; exact x.2.elim
  middle := by intro b c d e; funext ⟨_,s⟩; rcases s with (a | b) | (c | d) <;> rfl
theorem rightCross (a : Type u) : LinCross sumCross (Lin.right gather a) where
  dup := by funext x; cases x.1 <;> exact ‹PEmpty›.elim
  merge := by funext x; exact x.1.elim
  middle := by intro b c d e; funext ⟨s,_⟩; rcases s with (a | b) | (c | d) <;> rfl

/-- In reverse-function coefficients the flat entry charts can be chosen
independently: the equality no longer selects the column chart by pasting
the transpose to the row chart. This result uses actual tagged functions,
not the carrier bijection alone. -/
theorem independent_flat_ragged {X Y B : Type w} [DecidableEq (Triple X Y B)]
    (a : Type u) (V : X → Type u) (A : Y → B → Type u) (bs : Y → List B)
    (xs : List X) (ys : List Y)
    {q : Type u} (β : q → tensor.obj (fold sum PEmpty V xs) (fold sum PEmpty (fun y => fold sum PEmpty (A y) (bs y)) ys))
    {is : List (Triple X Y B)} (nodup : is.Nodup)
    (p : AddressOrder (Triple X Y B) is (rowTree bs xs ys).leaves)
    (r : AddressOrder (Triple X Y B) is (colTree bs xs ys).leaves) :
    flatRowRoute (H:=addStruct) (Lin.left left a) gather left V A bs xs ys foldLeafUnit β p =
    coeff.seq
      (GridExpr.chartFrom (H:=addStruct) foldLeafUnit
        (fun i => (a × (labels (T:=tensor) V A i))) (colTree bs xs ys) r)
      (coeff.seq (GridExpr.gatherE (Lin.left left a) (labels (T:=tensor) V A) (colTree bs xs ys))
        ((Lin.left left a).map (transportSource (eval_col_tree (T:=tensor) (S:=sum) (Z:=PEmpty) V A bs xs ys)
          (coeff.seq (raggedColGather gather left V xs ys bs A) β)))) := by
  rw [actual_ragged_flat sumCross (Lin.left left a) (leftGatherNatural.inner a) (leftCross a)
    gather left gridBinary V A bs xs ys foldLeafUnit β p]
  unfold flatColumnRoute
  rw [independent_charts _ nodup p r (chartC bs xs ys)]
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
