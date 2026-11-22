module

public import ContextualComposition.DependentFibre

@[expose] public section

/-! The addressed tensor portion of fixed-target dependent Fubini. The source
of this calculation is already distributed independently by occurrence. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {T S : Bi K} {Z : C}
/-- The input is just the binary middle-four structural arrow and its ordinary
naturality, plus a unit comparison. It has no finite shuffle or aggregate law. -/
structure Middle (T : Bi K) (U : C) where
  empty : K.Hom U (T.obj U U)
  cell (a b c d : C) : K.Hom (T.obj (T.obj a b) (T.obj c d)) (T.obj (T.obj a c) (T.obj b d))
  nat {a b c d a' b' c' d' : C}
    (p : K.Hom a a') (q : K.Hom b b') (r : K.Hom c c') (s : K.Hom d d') :
    K.seq (T.map (T.map p q) (T.map r s)) (cell a' b' c' d') =
      K.seq (cell a b c d) (T.map (T.map p r) (T.map q s))
variable {U : C} (M : Middle T U) {I : Type w}
def shuffle (A B : I → C) : (is : List I) →
    K.Hom (fold T U (fun i => T.obj (A i) (B i)) is)
      (T.obj (fold T U A is) (fold T U B is))
  | [] => M.empty
  | i::is => K.seq (T.map (K.id _) (shuffle A B is)) (M.cell (A i) (B i) _ _)
theorem shuffle_nat {A B A' B' : I → C} (p : ∀ i, K.Hom (A i) (A' i))
    (q : ∀ i, K.Hom (B i) (B' i)) (is : List I) :
    K.seq (act T U (fun i => T.map (p i) (q i)) is) (shuffle M A' B' is) =
    K.seq (shuffle M A B is) (T.map (act T U p is) (act T U q is)) := by
  induction is with
  | nil => simp only [act, shuffle, fold, T.map_id, K.id_seq, K.seq_id]
  | cons i is ih =>
    simp only [act, shuffle, fold]
    rw [← K.assoc, ← T.map_seq, K.seq_id, ih, K.assoc]
    rw [← M.nat, ← K.assoc, ← T.map_seq, K.id_seq]

/-- One piece of an ordered fixed-target fibre at an occurrence, split
immediately before and after the whole-fibre continuation operations. -/
structure Stage (T : Bi K) where
  src : C
  x : C
  y : C
  x' : C
  y' : C
  before : K.Hom src (T.obj x y)
  parent : K.Hom x x'
  cont : K.Hom y y'
variable (D : I → Stage T)
theorem addressed (is : List I) :
    K.seq (act T U (fun i => K.seq (D i).before (T.map (D i).parent (D i).cont)) is)
      (shuffle M (fun i => (D i).x') (fun i => (D i).y') is) =
    K.seq (act T U (fun i => (D i).before) is)
      (K.seq (shuffle M (fun i => (D i).x) (fun i => (D i).y) is)
        (T.map (act T U (fun i => (D i).parent) is) (act T U (fun i => (D i).cont) is))) := by
  rw [← act_seq, K.assoc, shuffle_nat]

variable (G : Gather S T Z) (L : LeftGather S T Z)
/-- The input addresses are carried by X. Repeated labels never identify
their positions. One row for every parent address, including rows with an
empty inner source. No arrow out of an empty sum is chosen canonically. -/
structure Fibre where
  X : Type w
  V : X → C
  J : Input X C
  xs : List X
  a : C
  b : C
  β : ∀ x, K.Hom (inner (S:=S) (Z:=Z) J x) b
  α : K.Hom (fold S Z V xs) a

def Fibre.stage (d : Fibre (S:=S) (Z:=Z)) : Stage T where
  src := fold S Z (rowSource (T:=T) (S:=S) (Z:=Z) d.V d.J) d.xs
  x := fold S Z d.V d.xs
  y := d.b
  x' := d.a
  y' := d.b
  before := K.seq (act S Z (row d.V d.J L d.β) d.xs) (gather G d.V d.b d.xs)
  parent := d.α
  cont := K.id d.b

theorem Fibre.stage_eq (d : Fibre (S:=S) (Z:=Z)) :
    K.seq (d.stage G L).before (T.map (d.stage G L).parent (d.stage G L).cont) =
      dep G d.V d.J L d.xs d.β d.α := K.assoc _ _ _

/-- After distribution into the tensor of occurrence domains, shuffle can
be moved before all parent merges. The continuation-dependent sums remain
on the input side, before these merges, on both routes. -/
theorem addressedDep (ds : I → Fibre (S:=S) (Z:=Z)) (is : List I) :
    K.seq (act T U (fun i => dep G (ds i).V (ds i).J L (ds i).xs (ds i).β (ds i).α) is)
      (shuffle M (fun i => (ds i).a) (fun i => (ds i).b) is) =
    K.seq (act T U (fun i => ((ds i).stage G L).before) is)
      (K.seq (shuffle M (fun i => fold S Z (ds i).V (ds i).xs) (fun i => (ds i).b) is)
        (T.map (act T U (fun i => (ds i).α) is) (act T U (fun i => K.id (ds i).b) is))) := by
  simpa only [Fibre.stage, dep, K.assoc] using addressed M (fun i => (ds i).stage G L) is
end ContextualComposition.NativeFinitePush.DependentFibre
