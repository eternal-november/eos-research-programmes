module
public import ContextualComposition.NativeRouteReduction
public import ContextualComposition.AbsorbingZero
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C} {H : AddStruct S Z}
structure AddInvertible (H : AddStruct S Z) where
  unit (a : C) : Inv (H.unitInv a)
  assoc (a b c : C) : Inv (H.assoc a b c)
  assocInv (a b c : C) : Inv (H.assocInv a b c)
  swap (a b : C) : Inv (H.swap a b)
variable (I : AddInvertible H) {X : Type w} (A : X → C)
def movePastInv (a b c : C) : Inv (movePast H a b c) :=
  (I.assocInv a b c).comp (((I.swap a b).tensor (Inv.ident c)).comp (I.assoc b a c))
def joinInv (xs ys : List X) : Inv (join H A xs ys) :=
  match xs with
  | [] => I.unit _
  | x::xs => ((Inv.ident (A x)).tensor (joinInv xs ys)).comp (I.assocInv _ _ _)
def flattenInv : (rows : List (List X)) → Inv (flatten H A rows)
  | [] => Inv.ident _
  | row::rows => (joinInv I A row rows.flatten).comp ((Inv.ident _).tensor (flattenInv rows))
def maskInv {xs ls rs} : (m : Mask X xs ls rs) → Inv (Mask.route H A m)
  | .nil => I.unit _
  | .take _ m => ((Inv.ident _).tensor (maskInv m)).comp (I.assocInv _ _ _)
  | .pass _ m => ((Inv.ident _).tensor (maskInv m)).comp (movePastInv I _ _ _)
def blocksInv {xs bs r} : (b : Blocks X xs bs r) → Inv (Blocks.group H A b)
  | .done _ => Inv.ident _
  | .step m b => (maskInv I A m).comp ((Inv.ident _).tensor (blocksInv b))
/-- An explicitly addressed reordering. Adjacent swaps remain real arrows,
even when their resource arguments happen to be equal. -/
inductive AddressOrder (X : Type w) : List X → List X → Type w where
  | ident (xs) : AddressOrder X xs xs
  | swap (x y) (xs) : AddressOrder X (x::y::xs) (y::x::xs)
  | keep (x) {xs ys} : AddressOrder X xs ys → AddressOrder X (x::xs) (x::ys)
  | seq {xs ys zs} : AddressOrder X xs ys → AddressOrder X ys zs → AddressOrder X xs zs
namespace AddressOrder
variable {A}
theorem ofPerm {xs ys : List X} : xs.Perm ys → Nonempty (AddressOrder X xs ys) := by
  intro p
  induction p with
  | nil => exact ⟨.ident []⟩
  | cons x _ ih => exact ih.elim fun r => ⟨.keep x r⟩
  | swap x y l => exact ⟨.swap y x l⟩
  | trans _ _ ih jh => exact ih.elim fun i => jh.elim fun j => ⟨.seq i j⟩
variable (H A)
def mapSum {xs ys} : AddressOrder X xs ys → K.Hom (fold S Z A xs) (fold S Z A ys)
  | .ident _ => K.id _
  | .swap x y _ => movePast H (A x) (A y) _
  | .keep x p => S.map (K.id (A x)) (mapSum p)
  | .seq p q => K.seq (mapSum p) (mapSum q)
variable {H A}
def mapSumInv {xs ys} : (p : AddressOrder X xs ys) → Inv (mapSum H A p)
  | .ident _ => Inv.ident _
  | .swap x y _ => movePastInv I (A x) (A y) _
  | .keep x p => (Inv.ident (A x)).tensor (mapSumInv p)
  | .seq p q => (mapSumInv p).comp (mapSumInv q)
end AddressOrder

/-- Nested branch chart distinct from a list of leaves. For a finite
dependent fibre it records empty child lists along with actual leaves. -/
inductive Branch (X : Type w) where
  | leaf (x : X)
  | rows (bs : List (Branch X))
namespace Branch
mutual
def leaves : Branch X → List X
  | .leaf x => [x]
  | .rows bs => leavesRows bs
def leavesRows : List (Branch X) → List X
  | [] => []
  | b::bs => leaves b ++ leavesRows bs
end
mutual
def obj : Branch X → C
  | .leaf x => fold S Z A [x]
  | .rows bs => objRows bs
def objRows : List (Branch X) → C
  | [] => Z
  | b::bs => S.obj (obj b) (objRows bs)
end
mutual
def chart : (b : Branch X) → K.Hom (fold S Z A b.leaves) (obj (S:=S) (Z:=Z) A b)
  | .leaf _ => K.id _
  | .rows bs => chartRows bs
def chartRows : (bs : List (Branch X)) → K.Hom (fold S Z A (leavesRows bs)) (objRows (S:=S) (Z:=Z) A bs)
  | [] => K.id _
  | b::bs => K.seq (join H A b.leaves (leavesRows bs))
      (S.map (chart b) (chartRows bs))
end
mutual
def chartInv : (b : Branch X) → Inv (chart (H:=H) A b)
  | .leaf _ => Inv.ident _
  | .rows bs => chartRowsInv bs
def chartRowsInv : (bs : List (Branch X)) → Inv (chartRows (H:=H) A bs)
  | [] => Inv.ident _
  | b::bs => (joinInv I A b.leaves (leavesRows bs)).comp ((chartInv b).tensor (chartRowsInv bs))
end
end Branch
/-- Change from the ordered flat fibre to a chosen branch chart. Equality can
be reflected through this map as well as preserved by it. An explicit
address order is required: merely matching coefficient objects is invalid. -/
def flatToChart {xs : List X} (b : Branch X) (p : AddressOrder X xs b.leaves) :=
  K.seq (AddressOrder.mapSum H A p) (Branch.chart (H:=H) A b)
def flatToChartInv {xs : List X} (b : Branch X) (p : AddressOrder X xs b.leaves) :
    Inv (flatToChart (H:=H) A b p) :=
  (AddressOrder.mapSumInv I p).comp (Branch.chartInv I A b)
include I in
theorem compareFlat {xs : List X} (b : Branch X) (p : AddressOrder X xs b.leaves)
    {q : C} {f g : K.Hom (Branch.obj (S:=S) (Z:=Z) A b) q} :
    K.seq (flatToChart (H:=H) A b p) f = K.seq (flatToChart (H:=H) A b p) g ↔ f = g :=
  ⟨(flatToChartInv I A b p).cancelL, fun h => congrArg (K.seq (flatToChart (H:=H) A b p)) h⟩
end ContextualComposition.NativeFinitePush.DependentFibre
