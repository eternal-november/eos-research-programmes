module

public import ContextualComposition.DependentComposition

@[expose] public section

/-! Comparing the two genuinely different structural routes at the outer
rectangle of binary Fubini after the continuations have been evaluated.
Separately additive naturality of the binary shuffle is required only on
the primitive zero and binary sum, not on any rectangle or native map. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}

structure Endo (K : Coeff C) where
  obj : C → C
  map : ∀ {a b}, K.Hom a b → K.Hom (obj a) (obj b)
  id : ∀ a, map (K.id a) = K.id (obj a)
  seq : ∀ {a b c} (p : K.Hom a b) (q : K.Hom b c), map (K.seq p q) = K.seq (map p) (map q)
structure Lin (S : Bi K) (Z : C) extends Endo K where
  nil : K.Hom Z (obj Z)
  cons (a b : C) : K.Hom (S.obj (obj a) (obj b)) (obj (S.obj a b))
abbrev Lin.comp (F G : Lin S Z) : Lin S Z where
  obj x := G.obj (F.obj x)
  map p := G.map (F.map p)
  id a := by rw [F.id, G.id]
  seq p q := by rw [F.seq, G.seq]
  nil := K.seq G.nil (G.map F.nil)
  cons a b := K.seq (G.cons _ _) (G.map (F.cons a b))
abbrev Lin.right (G : Gather S T Z) (b : C) : Lin S Z where
  obj a := T.obj a b
  map f := T.map f (K.id b)
  id _ := T.map_id _ _
  seq f g := by simpa only [K.id_seq] using T.map_seq f g (K.id b) (K.id b)
  nil := G.nil b
  cons a c := G.cons a c b
abbrev Lin.left (L : LeftGather S T Z) (b : C) : Lin S Z where
  obj a := T.obj b a
  map f := T.map (K.id b) f
  id _ := T.map_id _ _
  seq f g := by simpa only [K.id_seq] using T.map_seq (K.id b) (K.id b) f g
  nil := L.nil b
  cons a c := L.cons b a c

def Lin.collect (F : Lin S Z) {X : Type w} (A : X → C) : (xs : List X) →
    K.Hom (fold S Z (fun x => F.obj (A x)) xs) (F.obj (fold S Z A xs))
  | [] => F.nil
  | x::xs => K.seq (S.map (K.id _) (F.collect A xs)) (F.cons (A x) _)
structure LinSquare (F G : Lin S Z) (η : ∀ a, K.Hom (F.obj a) (G.obj a)) : Prop where
  nil : K.seq F.nil (η Z) = G.nil
  cons (a b : C) : K.seq (F.cons a b) (η (S.obj a b)) =
      K.seq (S.map (η a) (η b)) (G.cons a b)
theorem LinSquare.collect {F G : Lin S Z} {η} (h : LinSquare F G η) {X : Type w}
    (A : X → C) (xs : List X) :
    K.seq (F.collect A xs) (η (fold S Z A xs)) =
    K.seq (act S Z (fun x => η (A x)) xs) (G.collect A xs) := by
  induction xs with
  | nil => exact h.nil.trans (K.id_seq _).symm
  | cons x xs ih =>
    simp only [Lin.collect, act, fold, K.assoc, h.cons]
    rw [← K.assoc, ← S.map_seq, K.id_seq, ih, ← K.assoc, ← S.map_seq, K.seq_id]


variable {U : C} (M : Middle T U) (G : Gather S T Z) (L : LeftGather S T Z)
abbrev leftX (b y d : C) := (Lin.right G b).comp (Lin.right G (T.obj y d))
abbrev rightX (b y d : C) := (Lin.right G y).comp (Lin.right G (T.obj b d))
abbrev leftY (x b d : C) := (Lin.right G d).comp (Lin.left L (T.obj x b))
abbrev rightY (x b d : C) := (Lin.left L x).comp (Lin.right G (T.obj b d))

/-- Four primitive local diagrams: binary and empty separately in x and y.
No native maps, finite lists, composite partitions, or grids occur here. -/
structure MedialLinear : Prop where
  x (b y d : C) : LinSquare (leftX G b y d) (rightX G b y d) (fun a => M.cell a b y d)
  y (x b d : C) : LinSquare (leftY G L x b d) (rightY G L x b d) (fun c => M.cell x b c d)

variable {X Y : Type w} (V : X → C) (W : Y → C) (xs : List X) (ys : List Y) (b d : C)
def lhsGather :=
  K.seq (act S Z (fun x => (leftY G L (V x) b d).collect W ys) xs)
    ((leftX G b (fold S Z W ys) d).collect V xs)
def rhsGather :=
  K.seq (act S Z (fun x => (rightY G L (V x) b d).collect W ys) xs)
    ((rightX G b (fold S Z W ys) d).collect V xs)
theorem rectangle (H : MedialLinear M G L) :
    K.seq (lhsGather G L V W xs ys b d) (M.cell (fold S Z V xs) b (fold S Z W ys) d) =
    K.seq (act S Z (fun x => act S Z (fun y => M.cell (V x) b (W y) d) ys) xs)
      (rhsGather G L V W xs ys b d) := by
  unfold lhsGather rhsGather
  rw [K.assoc, (H.x b _ d).collect V xs, ← K.assoc, act_seq]
  simp only [(H.y _ b d).collect W ys]
  rw [← act_seq, K.assoc]

/-- Both routes, now with genuinely arbitrary whole-sum parent arrows.
The left route gathers each independent axis then merges and shuffles;
the right route shuffles entrywise then gathers and merges. -/
theorem rectangle_native (H : MedialLinear M G L) {a c : C}
    (α : K.Hom (fold S Z V xs) a) (γ : K.Hom (fold S Z W ys) c) :
    K.seq (lhsGather G L V W xs ys b d)
      (K.seq (T.map (T.map α (K.id b)) (T.map γ (K.id d))) (M.cell a b c d)) =
    K.seq (act S Z (fun x => act S Z (fun y => M.cell (V x) b (W y) d) ys) xs)
      (K.seq (rhsGather G L V W xs ys b d) (T.map (T.map α γ) (T.map (K.id b) (K.id d)))) := by
  rw [M.nat, ← K.assoc, rectangle M G L V W xs ys b d H, K.assoc]

def actRect {A B : X → Y → C} (p : ∀ x y, K.Hom (A x y) (B x y)) :=
  act S Z (fun x => act S Z (p x) ys) xs
theorem actRect_seq {A B D : X → Y → C} (p : ∀ x y, K.Hom (A x y) (B x y))
    (q : ∀ x y, K.Hom (B x y) (D x y)) :
    K.seq (actRect (S:=S) (Z:=Z) xs ys p) (actRect (S:=S) (Z:=Z) xs ys q) =
      actRect (S:=S) (Z:=Z) xs ys (fun x y => K.seq (p x y) (q x y)) := by
  simp only [actRect, act_seq]
/-- Binary native square on the outer product fibre. Each B x and D y may
be the entire continuation preimage sum at that parent; β, θ are arbitrary
maps out of those actual objects. The two routes differ before any merge:
one applies the continuation maps then shuffles, the other shuffles first
and tensors their actual maps. Both put each continuation before its
corresponding parent merge. The preceding transfer of the branch product
into this common row-major outer rectangle is not part of this theorem. -/
theorem rectangle_dependent (H : MedialLinear M G L) {a c : C}
    (B : X → C) (D : Y → C) (β : ∀ x, K.Hom (B x) b) (θ : ∀ y, K.Hom (D y) d)
    (α : K.Hom (fold S Z V xs) a) (γ : K.Hom (fold S Z W ys) c) :
    K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => T.map (T.map (K.id (V x)) (β x)) (T.map (K.id (W y)) (θ y))))
      (K.seq (lhsGather G L V W xs ys b d)
        (K.seq (T.map (T.map α (K.id b)) (T.map γ (K.id d))) (M.cell a b c d))) =
    K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => M.cell (V x) (B x) (W y) (D y)))
      (K.seq (actRect (S:=S) (Z:=Z) xs ys
          (fun x y => T.map (T.map (K.id (V x)) (K.id (W y))) (T.map (β x) (θ y))))
        (K.seq (rhsGather G L V W xs ys b d) (T.map (T.map α γ) (T.map (K.id b) (K.id d))))) := by
  rw [rectangle_native M G L V W xs ys b d H α γ]
  change K.seq _ (K.seq (actRect (S:=S) (Z:=Z) xs ys (fun x y => M.cell (V x) b (W y) d)) _) = _
  rw [← K.assoc, actRect_seq]
  rw [← K.assoc (actRect (S:=S) (Z:=Z) xs ys (fun x y => M.cell (V x) (B x) (W y) (D y))), actRect_seq]
  simp only [M.nat]

end ContextualComposition.NativeFinitePush.DependentFibre
