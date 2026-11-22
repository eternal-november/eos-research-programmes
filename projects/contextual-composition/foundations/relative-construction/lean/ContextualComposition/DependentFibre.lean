module

public import ContextualComposition.NativeFinitePush

@[expose] public section

/-! Fixed-final-fibre dependent accumulation, in a coefficient category with
two bifunctors. Additive lists are ordered and have a syntactic empty summand.
The gathering maps point from the explicit distributed domain toward the
factored tensor. No elementwise decomposition of actual arrows is used. -/
namespace ContextualComposition.NativeFinitePush
namespace DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C}
structure Bi (K : Coeff C) where
  obj : C → C → C
  map : ∀ {a b c d}, K.Hom a b → K.Hom c d → K.Hom (obj a c) (obj b d)
  map_id : ∀ a b, map (K.id a) (K.id b) = K.id (obj a b)
  map_seq : ∀ {a b c d e f} (p : K.Hom a b) (q : K.Hom b c) (r : K.Hom d e) (s : K.Hom e f),
    map (K.seq p q) (K.seq r s) = K.seq (map p r) (map q s)
variable (S T : Bi K) (Z : C)
def fold {X : Type w} (V : X → C) : List X → C
  | [] => Z
  | x::xs => S.obj (V x) (fold V xs)
def act {X : Type w} {V W : X → C} (p : ∀ x, K.Hom (V x) (W x)) :
    (xs : List X) → K.Hom (fold S Z V xs) (fold S Z W xs)
  | [] => K.id Z
  | x::xs => S.map (p x) (act p xs)
theorem act_seq {X : Type w} {V W D : X → C} (p : ∀ x, K.Hom (V x) (W x))
    (q : ∀ x, K.Hom (W x) (D x)) (xs : List X) :
    K.seq (act S Z p xs) (act S Z q xs) = act S Z (fun x => K.seq (p x) (q x)) xs := by
  induction xs with
  | nil => exact K.id_seq _
  | cons x xs ih => simp only [act, fold, ← S.map_seq, ih]

/-- Binary and nullary gathering in the first variable. Naturality is
required only in the fixed continuation variable, for these primitive maps. -/
structure Gather where
  nil (c : C) : K.Hom Z (T.obj Z c)
  cons (a b c : C) : K.Hom (S.obj (T.obj a c) (T.obj b c)) (T.obj (S.obj a b) c)
  nil_nat {c d : C} (q : K.Hom c d) : K.seq (nil c) (T.map (K.id Z) q) = nil d
  cons_nat (a b : C) {c d : C} (q : K.Hom c d) :
    K.seq (cons a b c) (T.map (K.id (S.obj a b)) q) =
    K.seq (S.map (T.map (K.id a) q) (T.map (K.id b) q)) (cons a b d)
variable {S T Z} (G : Gather S T Z)
def gather {X : Type w} (V : X → C) (c : C) : (xs : List X) →
    K.Hom (fold S Z (fun x => T.obj (V x) c) xs) (T.obj (fold S Z V xs) c)
  | [] => G.nil c
  | x::xs => K.seq (S.map (K.id _) (gather V c xs)) (G.cons (V x) _ c)
theorem gather_nat {X : Type w} (V : X → C) {c d : C} (q : K.Hom c d) (xs : List X) :
    K.seq (gather G V c xs) (T.map (K.id _) q) =
    K.seq (act S Z (fun x => T.map (K.id (V x)) q) xs) (gather G V d xs) := by
  induction xs with
  | nil => exact (G.nil_nat q).trans (K.id_seq _).symm
  | cons x xs ih =>
    simp only [gather, act, fold, K.assoc, G.cons_nat]
    rw [← K.assoc, ← S.map_seq, K.id_seq, ih, ← K.assoc, ← S.map_seq, K.seq_id]

variable {X : Type w} (V : X → C)
/-- Inner sums are explicit at each outer address; no constancy of the
first-stage continuation on the outer fibre is imposed. -/
structure Input (X : Type w) (C : Type u) where
  terms : X → List C
variable (J : Input X C)
abbrev inner (x : X) := fold S Z id (J.terms x)
abbrev rowSource (x : X) := fold S Z (fun b => T.obj (V x) b) (J.terms x)
/-- Left-variable-fixed distribution, in the gathering direction. -/
structure LeftGather (S T : Bi K) (Z : C) where
  nil (a : C) : K.Hom Z (T.obj a Z)
  cons (a b d : C) : K.Hom (S.obj (T.obj a b) (T.obj a d)) (T.obj a (S.obj b d))
def gatherLeft (L : LeftGather S T Z) (a : C) : (xs : List C) →
    K.Hom (fold S Z (T.obj a) xs) (T.obj a (fold S Z id xs))
  | [] => L.nil _
  | b::bs => K.seq (S.map (K.id _) (gatherLeft L a bs)) (L.cons _ b _)
variable (L : LeftGather S T Z)
def row {b : C} (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b) (x : X) :
    K.Hom (rowSource (S:=S) (Z:=Z) (T:=T) V J x) (T.obj (V x) b) :=
  K.seq (gatherLeft L (V x) (J.terms x)) (T.map (K.id _) (β x))
def dep {a b : C} (xs : List X) (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b)
    (α : K.Hom (fold S Z V xs) a) :
    K.Hom (fold S Z (rowSource (S:=S) (Z:=Z) (T:=T) V J) xs) (T.obj a b) :=
  K.seq (act S Z (row V J L β) xs) (K.seq (gather G V b xs) (T.map α (K.id _)))
theorem post {a b c d : C} (xs : List X) (β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b)
    (α : K.Hom (fold S Z V xs) a) (p : K.Hom a c) (q : K.Hom b d) :
    K.seq (dep G V J L xs β α) (T.map p q) =
      dep G V J L xs (fun x => K.seq (β x) q) (K.seq α p) := by
  have hex : K.seq (T.map α (K.id b)) (T.map p q) =
      K.seq (T.map (K.id _) q) (T.map (K.seq α p) (K.id d)) := by
    rw [← T.map_seq, ← T.map_seq, K.id_seq, K.id_seq, K.seq_id]
  have hr (x : X) : K.seq (row V J L β x) (T.map (K.id _) q) =
      row V J L (fun y => K.seq (β y) q) x := by
    unfold row
    rw [K.assoc, ← T.map_seq, K.id_seq]
  simp only [dep, K.assoc, hex]
  rw [← K.assoc (gather _ _ _ _), gather_nat, K.assoc, ← K.assoc (act _ _ _ _), act_seq]
  simp only [hr]
end DependentFibre
end ContextualComposition.NativeFinitePush
