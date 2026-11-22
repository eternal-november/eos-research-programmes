module

public import ContextualComposition.DependentCarrier

@[expose] public section

/-! Construct partition maps for finite addressed lists without any coproduct
universal property. The structural map from a flat sum to a grouped sum is
built from additive units, associator, and an adjacent swap. No equality of
resource labels is inspected. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S : Bi K} {Z : C}
structure AddStruct (S : Bi K) (Z : C) where
  unitInv (a : C) : K.Hom a (S.obj Z a)
  assoc (a b c : C) : K.Hom (S.obj (S.obj a b) c) (S.obj a (S.obj b c))
  assocInv (a b c : C) : K.Hom (S.obj a (S.obj b c)) (S.obj (S.obj a b) c)
  swap (a b : C) : K.Hom (S.obj a b) (S.obj b a)
variable (H : AddStruct S Z)
def movePast (a b c : C) : K.Hom (S.obj a (S.obj b c)) (S.obj b (S.obj a c)) :=
  K.seq (H.assocInv a b c) (K.seq (S.map (H.swap a b) (K.id c)) (H.assoc b a c))
/-- Inserting or crossing a branch block changes its coefficient sum by
honest categorical arrows, including insertion of an empty block. -/
def join {X : Type w} (A : X → C) (xs ys : List X) :
    K.Hom (fold S Z A (xs ++ ys)) (S.obj (fold S Z A xs) (fold S Z A ys)) :=
  match xs with
  | [] => H.unitInv _
  | x::ts => K.seq (S.map (K.id _) (join A ts ys)) (H.assocInv (A x) _ _)

def flatten {X : Type w} (A : X → C) : (rows : List (List X)) →
    K.Hom (fold S Z A rows.flatten) (fold S Z (fold S Z A) rows)
  | [] => K.id Z
  | xs::rs => K.seq (join H A xs rs.flatten) (S.map (K.id _) (flatten A rs))

variable {I : Type w} {X : Type w}
structure AddNat (H : AddStruct S Z) : Prop where
  unit {a b : C} (p : K.Hom a b) : K.seq p (H.unitInv b) =
    K.seq (H.unitInv a) (S.map (K.id Z) p)
  assoc {a b c d e f : C} (p : K.Hom a d) (q : K.Hom b e) (r : K.Hom c f) :
    K.seq (S.map (S.map p q) r) (H.assoc d e f) =
    K.seq (H.assoc a b c) (S.map p (S.map q r))
  inv {a b c d e f : C} (p : K.Hom a d) (q : K.Hom b e) (r : K.Hom c f) :
    K.seq (S.map p (S.map q r)) (H.assocInv d e f) =
    K.seq (H.assocInv a b c) (S.map (S.map p q) r)
  swap {a b c d : C} (p : K.Hom a c) (q : K.Hom b d) :
    K.seq (S.map p q) (H.swap c d) = K.seq (H.swap a b) (S.map q p)
variable {H} (N : AddNat H)
include N in
theorem movePast_nat {a b c d e f : C} (p : K.Hom a d) (q : K.Hom b e) (r : K.Hom c f) :
    K.seq (S.map p (S.map q r)) (movePast H d e f) =
    K.seq (movePast H a b c) (S.map q (S.map p r)) := by
  unfold movePast
  rw [← K.assoc, N.inv]
  simp only [K.assoc]
  rw [← K.assoc (S.map _ _), ← S.map_seq, N.swap, K.seq_id,
    ← K.id_seq r, S.map_seq, K.assoc, N.assoc, K.id_seq]


/-- A proof-relevant addressed partition carries the original sequence and
both target blocks in its type; no equivariance premise is used. -/
inductive Mask (X : Type w) : List X → List X → List X → Type w
  | nil : Mask X [] [] []
  | take (x : X) {xs ls rs} : Mask X xs ls rs → Mask X (x::xs) (x::ls) rs
  | pass (x : X) {xs ls rs} : Mask X xs ls rs → Mask X (x::xs) ls (x::rs)
namespace Mask
def build (p : X → Bool) (xs : List X) : (ls : List X) × (rs : List X) × Mask X xs ls rs :=
  match xs with
  | [] => ⟨[], [], .nil⟩
  | x::ys =>
    let ⟨ls,rs,m⟩ := build p ys
    if p x then ⟨x::ls,rs,.take x m⟩ else ⟨ls,x::rs,.pass x m⟩
theorem outputs (p : X → Bool) (xs : List X) :
    (build p xs).1 = xs.filter p ∧ (build p xs).2.1 = xs.filter (fun x => !(p x)) := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    rw [build]
    generalize build p xs = t at ih ⊢
    rcases t with ⟨ls,rs,m⟩
    change ls = _ ∧ rs = _ at ih
    cases hp : p x <;> simp [hp, ih.1, ih.2]
variable (H)
def route (A : X → C) {xs ls rs} : Mask X xs ls rs →
    K.Hom (fold S Z A xs) (S.obj (fold S Z A ls) (fold S Z A rs))
  | .nil => H.unitInv _
  | .take x m => K.seq (S.map (K.id _) (route A m)) (H.assocInv (A x) _ _)
  | .pass x m => K.seq (S.map (K.id _) (route A m)) (movePast H (A x) _ _)
variable {H}
include N in
theorem natural {A B : X → C} (ar : ∀ x, K.Hom (A x) (B x)) {xs ls rs} (m : Mask X xs ls rs) :
    K.seq (act S Z ar xs) (route H B m) =
    K.seq (route H A m) (S.map (act S Z ar ls) (act S Z ar rs)) := by
  induction m with
  | nil => simp only [act, route, fold, S.map_id, K.id_seq, K.seq_id]
  | take x m ih =>
    simp only [act, route, fold]
    rw [← K.assoc, ← S.map_seq, K.seq_id, ih, ← K.id_seq (ar x), S.map_seq, K.assoc, N.inv, K.assoc, K.id_seq]
  | pass x m ih =>
    simp only [act, route, fold]
    rw [← K.assoc, ← S.map_seq, K.seq_id, ih, ← K.id_seq (ar x), S.map_seq, K.assoc, movePast_nat N, K.assoc, K.id_seq]
end Mask

/-- Successive stable binary partitions into a list of target blocks,
with an explicit final remainder. -/
inductive Blocks (X : Type w) : List X → List (List X) → List X → Type w
  | done (xs) : Blocks X xs [] xs
  | step {xs ls rs bs r} : Mask X xs ls rs → Blocks X rs bs r → Blocks X xs (ls::bs) r
namespace Blocks
def build [DecidableEq I] (f : X → I) (xs : List X) : (js : List I) →
    (bs : List (List X)) × (r : List X) × Blocks X xs bs r
  | [] => ⟨[],xs,.done xs⟩
  | j::js =>
    let ⟨ls,rs,m⟩ := Mask.build (fun x => f x == j) xs
    let ⟨bs,r,b⟩ := build f rs js
    ⟨ls::bs,r,.step m b⟩
theorem remainder [DecidableEq I] (f : X → I) (xs : List X) (js : List I) (x : X) :
    x ∈ (build f xs js).2.1 ↔ x ∈ xs ∧ f x ∉ js := by
  induction js generalizing xs with
  | nil => simp [build]
  | cons j js ih =>
    rw [build]
    have h := (Mask.outputs (fun y => f y == j) xs).2
    generalize Mask.build (fun y => f y == j) xs = t at h ⊢
    rcases t with ⟨ls,rs,m⟩
    change rs = _ at h
    change x ∈ (build f rs js).2.1 ↔ _
    rw [ih, h]
    simp [and_assoc]
theorem complete [DecidableEq I] (f : X → I) (xs : List X) (js : List I)
    (all : ∀ x ∈ xs, f x ∈ js) : (build f xs js).2.1 = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x hx =>
    let h := (remainder f xs js x).mp hx
    h.2 (all x h.1)
def target (A : X → C) (r : List X) : List (List X) → C
  | [] => fold S Z A r
  | l::bs => S.obj (fold S Z A l) (target A r bs)
def actBlocks {A B : X → C} (p : ∀ x, K.Hom (A x) (B x)) (r : List X) :
    (bs : List (List X)) → K.Hom (target (S:=S) (Z:=Z) A r bs) (target (S:=S) (Z:=Z) B r bs)
  | [] => act S Z p r
  | l::bs => S.map (act S Z p l) (actBlocks p r bs)
variable (H)
def group (A : X → C) {xs bs r} : Blocks X xs bs r → K.Hom (fold S Z A xs) (target (S:=S) (Z:=Z) A r bs)
  | .done _ => K.id _
  | .step m b => K.seq (Mask.route H A m) (S.map (K.id _) (group A b))
variable {H}
include N in
theorem natural {A B : X → C} (p : ∀ x, K.Hom (A x) (B x)) {xs bs r} (b : Blocks X xs bs r) :
    K.seq (act S Z p xs) (group H B b) =
    K.seq (group H A b) (actBlocks p r bs) := by
  induction b with
  | done => simp only [actBlocks, group, target, K.id_seq, K.seq_id]
  | step m b ih =>
    simp only [group, actBlocks, target]
    rw [← K.assoc, Mask.natural N, K.assoc, ← S.map_seq, K.seq_id, ih, K.assoc, ← S.map_seq, K.id_seq]
include N in
theorem built_natural [DecidableEq I] (f : X → I) (xs : List X) (js : List I)
    {A B : X → C} (p : ∀ x, K.Hom (A x) (B x)) :
    let b := (build f xs js).2.2
    K.seq (act S Z p xs) (group H B b) = K.seq (group H A b) (actBlocks p _ _) :=
  natural N p _
end Blocks
end ContextualComposition.NativeFinitePush.DependentFibre
