module

public import ContextualComposition.FubiniIso

@[expose] public section

/-! A flat-source augmentation square over an actual stable outer partition.
Only occurrence members of a group must supply a continuation arrow. There is
one global augmentation on the target sum; empty target/fibre cases are not
discharged by any uniqueness principle. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z U : C}
variable {H : AddStruct S Z} (N : AddNat H) {G : Gather S T Z} (L : LeftGather S T Z)
variable (R : UnitCompat G U) {X : Type w} (V : X → C) (J : Input X C)

def actMem {A B : X → C} (xs : List X) (p : ∀ x ∈ xs, K.Hom (A x) (B x)) :
    K.Hom (fold S Z A xs) (fold S Z B xs) :=
  match xs with
  | [] => K.id _
  | x::ts => S.map (p x (by simp)) (actMem ts (fun y hy => p y (by simp [hy])))
theorem actMem_eq {A B : X → C} (xs : List X) (p : ∀ x, K.Hom (A x) (B x)) :
    actMem (S:=S) (Z:=Z) xs (fun x _ => p x) = act S Z p xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [actMem, act, fold, ih]

theorem actMem_post {A B D : X → C} (xs : List X) (p : ∀ x ∈ xs, K.Hom (A x) (B x))
    (q : ∀ x, K.Hom (B x) (D x)) :
    K.seq (actMem (S:=S) (Z:=Z) xs p) (act S Z q xs) =
    actMem xs (fun x hx => K.seq (p x hx) (q x)) := by
  induction xs with
  | nil => exact K.id_seq _
  | cons x xs ih => simp only [actMem, act, fold, ← S.map_seq, ih]

def rowAt {b : C} (x : X) (β : K.Hom (inner (S:=S) (Z:=Z) J x) b) :
    K.Hom (rowSource (S:=S) (Z:=Z) (T:=T) V J x) (T.obj (V x) b) :=
  K.seq (gatherLeft L (V x) (J.terms x)) (T.map (K.id _) β)
def sourceRow (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U) (x : X) :=
  K.seq (rowAt L V J x (δ x)) (R.ρ (V x))
def localDep (xs : List X) {a b : C} (α : K.Hom (fold S Z V xs) a)
    (β : ∀ x ∈ xs, K.Hom (inner (S:=S) (Z:=Z) J x) b) :=
  K.seq (actMem (S:=S) (Z:=Z) xs (fun x hx => rowAt L V J x (β x hx)))
    (K.seq (gather G V b xs) (T.map α (K.id b)))

theorem localAug (xs : List X) {a b : C} (α : K.Hom (fold S Z V xs) a)
    (β : ∀ x ∈ xs, K.Hom (inner (S:=S) (Z:=Z) J x) b)
    (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U) (δ' : K.Hom b U)
    (law : ∀ x hx, K.seq (β x hx) δ' = δ x) :
    K.seq (localDep (G:=G) L V J xs α β) (K.seq (T.map (K.id a) δ') (R.ρ a)) =
      K.seq (act S Z (sourceRow L R V J δ) xs) α := by
  have h : K.seq (T.map α (K.id b)) (T.map (K.id a) δ') =
      K.seq (T.map (K.id _) δ') (T.map α (K.id U)) := by
    rw [← T.map_seq, ← T.map_seq, K.id_seq, K.seq_id, K.id_seq, K.seq_id]
  unfold localDep
  simp only [K.assoc]
  rw [← K.assoc (T.map α _), h, K.assoc, R.natural, ← K.assoc (gather _ _ _ _),
    gather_nat, K.assoc, ← K.assoc (gather _ _ _ _), gather_unit]
  rw [← K.assoc (act S Z _ xs), act_seq, ← K.assoc, actMem_post]
  congr 1
  rw [← actMem_eq xs (sourceRow L R V J δ)]
  congr 1
  funext x hx
  simp only [sourceRow, rowAt, K.assoc, ← K.assoc (T.map _ _), ← T.map_seq, K.id_seq, law]

/-- A list of entire outer-merge cells with target continuation augmentations.
Its index is a list of *blocks*, not a list of target objects: repeated target
objects can carry different cells. The remainder is treated separately. -/
inductive Layer (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U) :
    List (List X) → Type (max u v w)
  | nil : Layer δ []
  | cons {xs bs} (a b : C) (α : K.Hom (fold S Z V xs) a)
      (β : ∀ x ∈ xs, K.Hom (inner (S:=S) (Z:=Z) J x) b) (δ' : K.Hom b U)
      (law : ∀ x hx, K.seq (β x hx) δ' = δ x) (tail : Layer δ bs) : Layer δ (xs::bs)

namespace Layer
variable {V J} {δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U}
def out {bs} : Layer V J δ bs → C
  | .nil => Z
  | .cons a _ _ _ _ _ tail => S.obj a (out tail)
def productOut {bs} : Layer V J δ bs → C
  | .nil => Z
  | .cons a b _ _ _ _ tail => S.obj (T.obj a b) (productOut tail)
def outer {bs} (l : Layer V J δ bs) :
    K.Hom (Blocks.target (S:=S) (Z:=Z) V [] bs) l.out :=
  match l with
  | .nil => K.id Z
  | .cons _ _ α _ _ _ tail => S.map α (outer tail)
def depMap {bs} (l : Layer V J δ bs) :
    K.Hom (Blocks.target (S:=S) (Z:=Z) (rowSource (S:=S) (Z:=Z) (T:=T) V J) [] bs)
      (productOut (T:=T) l) :=
  match l with
  | .nil => K.id Z
  | .cons _ _ α β _ _ tail => S.map (localDep (G:=G) L V J _ α β) (depMap tail)
def targetRows {bs} (l : Layer V J δ bs) : K.Hom (productOut (T:=T) l) l.out :=
  match l with
  | .nil => K.id Z
  | .cons a _ _ _ δ' _ tail => S.map (K.seq (T.map (K.id a) δ') (R.ρ a)) (targetRows tail)
theorem square {bs} (l : Layer V J δ bs) :
    K.seq (depMap (G:=G) L l) (targetRows R l) =
    K.seq (Blocks.actBlocks (sourceRow L R V J δ) [] bs) l.outer := by
  induction l with
  | nil => rfl
  | cons a b α β δ' law tail ih =>
    simp only [depMap, targetRows, Blocks.actBlocks, outer, Blocks.target, productOut, out, ← S.map_seq]
    rw [localAug L R V J _ α β δ δ' law, ih]
end Layer

include N in
/-- The actual flat-source square: first partition by outer target, then
apply all dependent cells and the target's one global augmentation. Equality
to source augmentation follows from partition naturality and the native
outer augmentation equation; the analogous inner equations live in Layer.
The inner maps are on complete continuation sums, not yet derived by
partitioning arbitrary continuation carrier maps g. -/
theorem flat_augmentation {xs : List X} {bs : List (List X)} (part : Blocks X xs bs [])
    (δ : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) U) (l : Layer V J δ bs)
    (ε' : K.Hom l.out U) (ε : K.Hom (fold S Z V xs) U)
    (outer : K.seq (Blocks.group H V part) (K.seq l.outer ε') = ε) :
    K.seq (Blocks.group H (rowSource (T:=T) (S:=S) (Z:=Z) V J) part)
      (K.seq (l.depMap (G:=G) L) (K.seq (l.targetRows R) ε')) =
    K.seq (act S Z (sourceRow L R V J δ) xs) ε := by
  rw [← K.assoc (l.depMap L), Layer.square, K.assoc, ← K.assoc, ← Blocks.natural N, K.assoc, outer]

end ContextualComposition.NativeFinitePush.DependentFibre
