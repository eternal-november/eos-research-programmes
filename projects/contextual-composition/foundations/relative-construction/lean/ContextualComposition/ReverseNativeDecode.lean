module
public import ContextualComposition.ReverseContextChart
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
set_option backward.isDefEq.respectTransparency false
universe u w
variable {X : Type w} (V Y : X → Type u)
theorem lookup_act (p : ∀ i, Y i → V i) (xs : List X) (z : fold sum PEmpty Y xs) :
    lookup xs (act sum PEmpty p xs z) = ⟨(lookup xs z).1, p _ (lookup xs z).2⟩ := by
  induction xs with
  | nil => exact z.elim
  | cons x xs ih => cases z with | inl a => rfl | inr a => exact ih a
theorem lookup_gather (b : Type u) (xs : List X) (a : fold sum PEmpty V xs) (z : b) :
    lookup xs (DependentFibre.gather gather V b xs (a,z)) =
      ⟨(lookup xs a).1,((lookup xs a).2,z)⟩ := by
  induction xs with
  | nil => exact a.elim
  | cons x xs ih => cases a with | inl a => rfl | inr a => exact ih a

variable {B : Type w} (W : B → Type u) (a : Type u)
def unFoldMap (bs : List B) : fold sum PEmpty id (bs.map W) → fold sum PEmpty W bs :=
  match bs with
  | [] => PEmpty.elim
  | _::bs => fun | .inl x => .inl x | .inr t => .inr (unFoldMap bs t)
theorem unFoldMap_round (bs : List B) (x : fold sum PEmpty W bs) :
    unFoldMap W bs (foldMapObj W bs x) = x := by
  induction bs with
  | nil => exact x.elim
  | cons b bs ih => cases x with | inl => rfl | inr t => exact congrArg Sum.inr (ih t)

def unFoldTensor (bs : List B) :
    fold sum PEmpty (tensor.obj a) (bs.map W) → fold sum PEmpty (fun b => tensor.obj a (W b)) bs :=
  match bs with
  | [] => PEmpty.elim
  | _::bs => fun | .inl x => .inl x | .inr t => .inr (unFoldTensor bs t)
theorem lookup_left (bs : List B) (x : fold sum PEmpty id (bs.map W)) (v : a) :
    lookup bs (unFoldTensor W a bs (gatherLeft left a (bs.map W) (v,x))) =
      ⟨(lookup bs (unFoldMap W bs x)).1,(v,(lookup bs (unFoldMap W bs x)).2)⟩ := by
  induction bs with
  | nil => exact x.elim
  | cons b bs ih => cases x with | inl => rfl | inr t => exact ih t
variable {d : Carrier} {V : Fin d.n → Type u} {V' : Fin d.m → Type u}
variable {W : ∀ x, Fin (d.k x) → Type u} {W' : ∀ j, Fin (d.l j) → Type u}
variable (h : NativePair d V V' W W')
def chooseChild {j : Fin d.m} (z : Fin (d.l j)) (p : d.Parent j) (v : W' j z) :
    (y : Fin (d.k p.val)) × W p.val y := by
  rcases p with ⟨x,e⟩
  subst j
  exact ⟨(h.child x z v).1.val,(h.child x z v).2⟩
def decodeCell (j : Fin d.m) (z : Fin (d.l j))
    (v : fold sum PEmpty
      (fun p : d.Parent j => fold sum PEmpty (tensor.obj (V p.val)) ((d.children p z).map (W p.val)))
      (d.parents j)) :
    (p : d.Parent j) × (y : Fin (d.k p.val)) × (V p.val × W p.val y) :=
  let p := lookup (d.parents j) v
  let c := lookup (d.children p.1 z) (unFoldTensor (W p.1.val) (V p.1.val) _ p.2)
  ⟨p.1,c.1,c.2⟩

theorem decode_component (j : Fin d.m) (z : Fin (d.l j)) (a : V' j) (b : W' j z) :
    decodeCell (V:=V) (W:=W) j z ((nativePairData V' V W W' h).component gather left j z (a,b)) =
      let t := h.parent j a
      let s := chooseChild h z t.1 b
      ⟨t.1,s.1,(t.2,s.2)⟩ := by
  let p := h.parent j a
  let β := (nativePairData V' V W W' h).cont j z
  let α := (nativePairData V' V W W' h).outer j
  let J : Input (d.Parent j) (Type u) := ((nativePairData V' V W W' h).fibre j z).J
  have hp : lookup (d.parents j) (α a) = ⟨p.1,p.2⟩ :=
    lookup_inject _ _ _ _
  have hr :
    lookup (d.parents j) ((nativePairData V' V W W' h).component gather left j z (a,b)) =
      (⟨p.1,row (fun t : d.Parent j => V t.val) J left β p.1 (p.2,b)⟩ :
        Sigma (fun t : d.Parent j => fold sum PEmpty (tensor.obj (V t.val)) ((d.children t z).map (W t.val)))) := by
    unfold PairData.component dep
    change lookup (d.parents j) ((act sum PEmpty (row (fun t : d.Parent j => V t.val) J left β)
      (d.parents j)) (DependentFibre.gather gather (fun t : d.Parent j => V t.val) _ (d.parents j) (α a,b))) = _
    rw [lookup_act, lookup_gather, hp]
  unfold decodeCell
  rw [hr]
  have hlocal (t : d.Parent j) (u : V t.val) :
      lookup (d.children t z) (unFoldTensor (W t.val) (V t.val) _
        (row (fun t : d.Parent j => V t.val) J left β t (u,b))) =
      ⟨(chooseChild h z t b).1,(u,(chooseChild h z t b).2)⟩ := by
    rcases t with ⟨x,e⟩
    subst j
    unfold row
    change lookup (d.children ⟨x,rfl⟩ z) (unFoldTensor (W x) (V x) _
      (gatherLeft left (V x) _ (u,β ⟨x,rfl⟩ b))) = _
    rw [lookup_left]
    let c := h.child x z b
    have e₁ : β ⟨x,rfl⟩ b = foldMapObj (W x) _ (inject (d.children ⟨x,rfl⟩ z) c.1.val
      (mem_fibreList.mpr c.1.property) c.2) := rfl
    rw [e₁, unFoldMap_round, lookup_inject]
    rfl
  exact congrArg (fun c : (y : Fin (d.k p.1.val)) × (V p.1.val × W p.1.val y) => (⟨p.1,c⟩ : (t : d.Parent j) × (y : Fin (d.k t.val)) × (V t.val × W t.val y))) (hlocal p.1 p.2)
end ContextualComposition.NativeFinitePush.DependentFibre.ReverseType
