module

public import ContextualComposition.ReverseTypeRig

@[expose] public section

/-! From actual reverse-function native arrows to the ordered ragged fibre
input, retaining the chosen resource and source address. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
universe u w
variable {X : Type w} {A : X → Type u}
def inject [DecidableEq X] (xs : List X) (i : X) (hi : i ∈ xs) (v : A i) :
    fold sum PEmpty A xs :=
  match xs with
  | [] => False.elim (List.not_mem_nil hi)
  | x::ys => if h : i = x then .inl (h ▸ v) else .inr (inject ys i ((List.mem_cons.mp hi).resolve_left h) v)
theorem lookup_inject [DecidableEq X] (xs : List X) (i : X) (hi : i ∈ xs) (v : A i) :
    lookup xs (inject xs i hi v) = ⟨i,v⟩ := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons x xs ih =>
    by_cases h : i = x
    · subst x; simp [inject,lookup]
    · simp [inject, h, lookup, ih]
theorem lookup_mem (xs : List X) (v : fold sum PEmpty A xs) : (lookup xs v).1 ∈ xs := by
  induction xs with
  | nil => exact v.elim
  | cons x xs ih =>
    cases v with
    | inl a => exact List.mem_cons_self
    | inr b => exact List.mem_cons_of_mem _ (ih b)
theorem inject_lookup [DecidableEq X] (xs : List X) (nd : xs.Nodup) (v : fold sum PEmpty A xs) :
    inject xs (lookup xs v).1 (lookup_mem xs v) (lookup xs v).2 = v := by
  induction xs with
  | nil => exact v.elim
  | cons x xs ih =>
    cases v with
    | inl a => simp [lookup,inject]; rfl
    | inr b =>
      have ne : (lookup xs b).1 ≠ x := fun h => (List.nodup_cons.mp nd).1 (h ▸ lookup_mem xs b)
      simp [lookup,inject,ne,ih (List.nodup_cons.mp nd).2]; rfl
/-- Packing is injective on tagged resources even when the same coefficient
type occurs at several distinct addresses. -/
theorem inject_tagged [DecidableEq X] (xs : List X) {i j : X} (hi : i ∈ xs) (hj : j ∈ xs)
    (v : A i) (w : A j) (h : inject xs i hi v = inject xs j hj w) :
    (Sigma.mk i v : Sigma A) = ⟨j,w⟩ := by
  simpa only [lookup_inject] using congrArg (lookup xs) h

/-- Map between two dependent objects along an explicitly retained equality.
The coefficient can contain repeated labels; no conversion follows from
equality of those labels alone. -/
def foldMapObj {X : Type w} (A : X → Type u) : (xs : List X) →
    fold sum PEmpty A xs → fold sum PEmpty id (xs.map A)
  | [], v => v.elim
  | _::_, .inl a => .inl a
  | _::xs, .inr v => .inr (foldMapObj A xs v)

variable {d : Carrier} (Vp : Fin d.m → Type u) (V : Fin d.n → Type u)
variable (W : ∀ x, Fin (d.k x) → Type u) (Wp : ∀ j, Fin (d.l j) → Type u)
/-- This data is equivalent to native Hom cells over the specified carrier
maps: each target token recovers both a source position in the *whole* fibre
and its coefficient. -/
structure NativePair (d : Carrier) (V : Fin d.n → Type u) (Vp : Fin d.m → Type u)
    (W : ∀ x, Fin (d.k x) → Type u) (Wp : ∀ j, Fin (d.l j) → Type u) where
  parent : ∀ j, Vp j → fibre d.f V j
  child : ∀ x t, Wp (d.f x) t → fibre (d.g x) (W x) t

def nativePairData (h : NativePair d V Vp W Wp) : PairData sum PEmpty d where
  V := V
  W := W
  V' := Vp
  W' := Wp
  outer j a :=
    let p := h.parent j a
    inject (A:=fun p => V p.val) (d.parents j) p.1 (d.parent_mem p.1) p.2
  cont j z p v := by
    rcases p with ⟨x,hx⟩
    subst j
    let a := h.child x z v
    exact foldMapObj (W x) _ (inject (A:=W x) (d.children ⟨x,rfl⟩ z) a.1.val
      (mem_fibreList.mpr a.1.property) a.2)

/-- Arrow-family input rather than separate functions on leaves. -/
structure Pair where
  source : Family (Type u)
  target : Family (Type u)
  srcCont : Fin source.n → Family (Type u)
  dstCont : Fin target.n → Family (Type u)
  parent : Hom push source target
  child : ∀ x, Hom push (srcCont x) (dstCont (parent.addr x))
namespace Pair
def carrier (p : Pair.{u}) : Carrier where
  n := p.source.n
  m := p.target.n
  k x := (p.srcCont x).n
  l x := (p.dstCont x).n
  f := p.parent.addr
  g x := (p.child x).addr
def data (p : Pair.{u}) : PairData sum PEmpty p.carrier :=
  nativePairData p.target.val p.source.val (fun x => (p.srcCont x).val)
    (fun y => (p.dstCont y).val) ⟨p.parent.cell, fun x => (p.child x).cell⟩
def atTarget (p : Pair.{u}) (j : Fin p.target.n) (z : Fin (p.dstCont j).n) :=
  p.data.fibre j z

/-- Binary kernel specialized to arrows of the native category, not data
postulated separately from its actual coefficient and carrier functions. -/
theorem ragged (p q : Pair.{u}) (i : Fin p.target.n) (j : Fin q.target.n)
    (s : Fin (p.dstCont i).n) (t : Fin (q.dstCont j).n) :
    let e := p.atTarget i s
    let f := q.atTarget j t
    separate middle gather left e.V f.V e.xs f.xs e.J.terms f.J.terms e.b f.b e.β f.β e.α f.α =
    together middle gather left e.V f.V e.xs f.xs e.J.terms f.J.terms e.b f.b e.β f.β e.α f.α :=
  ragged_binary middle gather left _ _ _ _ _ _ _ _ _ _ _ _ outerLaws innerLaws
end Pair
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
