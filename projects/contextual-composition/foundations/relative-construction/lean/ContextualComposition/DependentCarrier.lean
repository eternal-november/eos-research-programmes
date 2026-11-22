module

public import ContextualComposition.RectangularFibre

@[expose] public section

/-! Attach the fixed-target calculation to arbitrary finite dependent carrier
maps. The list of parents is the ordered preimage with equality witnesses;
each continuation target is transported along its parent's witness. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v
variable {C : Type u} {K : Coeff.{u,v} C} {T S : Bi K} {Z U : C}

structure Carrier where
  n : Nat
  m : Nat
  k : Fin n → Nat
  l : Fin m → Nat
  f : Fin n → Fin m
  g : ∀ x, Fin (k x) → Fin (l (f x))

namespace Carrier
variable (d : Carrier)
def map (p : (x : Fin d.n) × Fin (d.k x)) : (j : Fin d.m) × Fin (d.l j) :=
  ⟨d.f p.1, d.g p.1 p.2⟩
abbrev Parent (j : Fin d.m) := {x : Fin d.n // d.f x = j}
def parents (j : Fin d.m) : List (d.Parent j) :=
  (fibreList d.f j).pmap (fun x h => ⟨x,h⟩) (fun _ hx => mem_fibreList.mp hx)
def lower {j : Fin d.m} (p : d.Parent j) (z : Fin (d.l j)) : Fin (d.l (d.f p.val)) :=
  Fin.cast (congrArg d.l p.property.symm) z
def children {j : Fin d.m} (p : d.Parent j) (z : Fin (d.l j)) : List (Fin (d.k p.val)) :=
  fibreList (d.g p.val) (d.lower p z)
theorem parent_mem {j : Fin d.m} (p : d.Parent j) : p ∈ d.parents j := by
  simp only [parents, List.mem_pmap]
  exact ⟨p.val, mem_fibreList.mpr p.property, rfl⟩
theorem child_mem {j : Fin d.m} (p : d.Parent j) (z : Fin (d.l j)) (y : Fin (d.k p.val)) :
    y ∈ d.children p z ↔ d.map ⟨p.val,y⟩ = ⟨j,z⟩ := by
  rcases p with ⟨x,h⟩
  subst j
  simp [children, lower, Carrier.map, mem_fibreList]
end Carrier

/-- Resource-labelled native dependent-pair data. No forward map from each
individual resource, injectivity, augmentation or zero uniqueness is assumed. -/
structure PairData (S : Bi K) (Z : C) (d : Carrier) where
  V : Fin d.n → C
  W : ∀ x, Fin (d.k x) → C
  V' : Fin d.m → C
  W' : ∀ j, Fin (d.l j) → C
  outer (j : Fin d.m) : K.Hom (fold S Z (fun p : d.Parent j => V p.val) (d.parents j)) (V' j)
  cont (j : Fin d.m) (z : Fin (d.l j)) (p : d.Parent j) :
    K.Hom (fold S Z id ((d.children p z).map (W p.val))) (W' j z)

def PairData.fibre {d : Carrier} (D : PairData S Z d) (j : Fin d.m) (z : Fin (d.l j)) :
    Fibre (S:=S) (Z:=Z) where
  X := d.Parent j
  xs := d.parents j
  V p := D.V p.val
  J := ⟨fun p => (d.children p z).map (D.W p.val)⟩
  α := D.outer j
  β := D.cont j z
  a := D.V' j
  b := D.W' j z

def PairData.component {d : Carrier} (D : PairData S Z d) (G : Gather S T Z) (L : LeftGather S T Z)
    (j : Fin d.m) (z : Fin (d.l j)) :=
  let b := D.fibre j z
  dep G b.V b.J L b.xs b.β b.α

theorem PairData.compat {d : Carrier} (D : PairData S Z d) (G : Gather S T Z)
    (L : LeftGather S T Z) (j : Fin d.m) (z : Fin (d.l j)) {a b : C}
    (p : K.Hom (D.V' j) a) (q : K.Hom (D.W' j z) b) :
    K.seq (D.component G L j z) (T.map p q) =
    dep G (D.fibre j z).V (D.fibre j z).J L (d.parents j)
      (fun x => K.seq (D.cont j z x) q) (K.seq (D.outer j) p) :=
  post G _ _ _ _ _ _ p q
end ContextualComposition.NativeFinitePush.DependentFibre
