module

public import ContextualComposition.DependentAugmentation

@[expose] public section

/-! The carrier equivalence and the actual coefficient isomorphism of
dependent Fubini. Neither inverse laws nor naturality are inferred merely
from equality of endpoint objects. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w t s
variable {C : Type u} {K : Coeff.{u,v} C} {T : Bi K} {U : C}
structure Inv {a b : C} (f : K.Hom a b) where
  inv : K.Hom b a
  hi : K.seq f inv = K.id a
  ih : K.seq inv f = K.id b
def Inv.ident (a : C) : Inv (K.id a) := ⟨K.id a,K.id_seq _,K.id_seq _⟩
def Inv.comp {a b c : C} {f : K.Hom a b} {g : K.Hom b c} (p : Inv f) (q : Inv g) :
    Inv (K.seq f g) where
  inv := K.seq q.inv p.inv
  hi := by rw [K.assoc, ← K.assoc g, q.hi, K.id_seq, p.hi]
  ih := by rw [K.assoc, ← K.assoc p.inv, p.ih, K.id_seq, q.ih]
def Inv.tensor {a b c d : C} {f : K.Hom a b} {g : K.Hom c d} (p : Inv f) (q : Inv g) :
    Inv (T.map f g) where
  inv := T.map p.inv q.inv
  hi := by rw [← T.map_seq, p.hi, q.hi, T.map_id]
  ih := by rw [← T.map_seq, p.ih, q.ih, T.map_id]

structure MiddleInv (M : Middle T U) where
  empty : Inv M.empty
  cell (a b c d : C) : Inv (M.cell a b c d)
variable {M : Middle T U} (P : MiddleInv M)
def shuffleInv {I : Type w} (A B : I → C) : (is : List I) → Inv (shuffle M A B is)
  | [] => P.empty
  | i::is => (Inv.tensor (Inv.ident _) (shuffleInv A B is)).comp (P.cell (A i) (B i) _ _)

def carrierTo {I : Type w} {X : I → Type t} {Y : (i : I) → X i → Type s}
    (p : (i : I) → Sigma (Y i)) : (x : (i : I) → X i) × ((i : I) → Y i (x i)) :=
  ⟨fun i => (p i).1,fun i => (p i).2⟩
def carrierFrom {I : Type w} {X : I → Type t} {Y : (i : I) → X i → Type s}
    (p : (x : (i : I) → X i) × ((i : I) → Y i (x i))) : (i : I) → Sigma (Y i) :=
  fun i => ⟨p.1 i,p.2 i⟩
theorem carrierTo_from {I : Type w} {X : I → Type t} {Y : (i : I) → X i → Type s}
    (p : (x : (i : I) → X i) × ((i : I) → Y i (x i))) : carrierTo (carrierFrom p) = p := rfl
theorem carrierFrom_to {I : Type w} {X : I → Type t} {Y : (i : I) → X i → Type s}
    (p : (i : I) → Sigma (Y i)) : carrierFrom (carrierTo p) = p := rfl
theorem carrier_natural {I : Type w} {X X' : I → Type t}
    {Y : (i : I) → X i → Type s} {Y' : (i : I) → X' i → Type s}
    (f : ∀ i, X i → X' i) (g : ∀ i x, Y i x → Y' i (f i x)) (p : (i : I) → Sigma (Y i)) :
    carrierTo (Y:=Y') (fun i => ⟨f i (p i).1,g i _ (p i).2⟩) =
      ⟨fun i => f i ((carrierTo p).1 i),fun i => g i _ ((carrierTo p).2 i)⟩ := rfl
end ContextualComposition.NativeFinitePush.DependentFibre
