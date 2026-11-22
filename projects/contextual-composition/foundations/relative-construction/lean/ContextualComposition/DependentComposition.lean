module

public import ContextualComposition.GlobalAugmentation

@[expose] public section

/-! Two native merge levels on the partitioned fibre. The second-stage
continuation varies by intermediate parent; within that parent's fibre
it is constant and can pass its first aggregate. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre
universe u v w
variable {C : Type u} {K : Coeff.{u,v} C} {S T : Bi K} {Z : C}
variable {G : Gather S T Z} (L : LeftGather S T Z)
structure GatherOuterNat (G : Gather S T Z) : Prop where
  cons {a a' b b' : C} (p : K.Hom a a') (q : K.Hom b b') (c : C) :
    K.seq (S.map (T.map p (K.id c)) (T.map q (K.id c))) (G.cons a' b' c) =
    K.seq (G.cons a b c) (T.map (S.map p q) (K.id c))
variable (N : GatherOuterNat G)
include N in
theorem gather_outer {I : Type w} {A B : I → C} (p : ∀ i, K.Hom (A i) (B i)) (c : C) (is : List I) :
    K.seq (act S Z (fun i => T.map (p i) (K.id c)) is) (gather G B c is) =
    K.seq (gather G A c is) (T.map (act S Z p is) (K.id c)) := by
  induction is with
  | nil => simp only [act, gather, fold, T.map_id, K.id_seq, K.seq_id]
  | cons i is ih =>
    simp only [act, gather, fold]
    rw [← K.assoc, ← S.map_seq, K.seq_id, ih, ← K.id_seq (T.map (p i) (K.id c)),
      S.map_seq, K.assoc, N.cons, K.assoc]

/-- Gathering all first-level rows after their continuations but before
their parents merge. This is the stage that would be lost if an aggregate
were silently replaced with a family of per-source maps. -/
def beforeParent (d : Fibre (S:=S) (Z:=Z)) {c : C} (q : K.Hom d.b c) :=
  K.seq (act S Z (row d.V d.J L (fun x => K.seq (d.β x) q)) d.xs) (gather G d.V c d.xs)

theorem first_exchange (d : Fibre (S:=S) (Z:=Z)) {c : C} (q : K.Hom d.b c) :
    K.seq (dep G d.V d.J L d.xs d.β d.α) (T.map (K.id d.a) q) =
      K.seq (beforeParent (G:=G) L d q) (T.map d.α (K.id c)) := by
  rw [post, K.seq_id]
  exact (K.assoc _ _ _).symm

include N in
theorem two_stage {I : Type w} (ds : I → Fibre (S:=S) (Z:=Z)) (is : List I)
    {c a : C} (q : ∀ i, K.Hom (ds i).b c)
    (α' : K.Hom (fold S Z (fun i => (ds i).a) is) a) :
    K.seq (act S Z (fun i => dep G (ds i).V (ds i).J L (ds i).xs (ds i).β (ds i).α) is)
      (K.seq (act S Z (fun i => T.map (K.id (ds i).a) (q i)) is)
        (K.seq (gather G (fun i => (ds i).a) c is) (T.map α' (K.id c)))) =
    K.seq (act S Z (fun i => beforeParent (G:=G) L (ds i) (q i)) is)
      (K.seq (gather G (fun i => fold S Z (ds i).V (ds i).xs) c is)
        (T.map (K.seq (act S Z (fun i => (ds i).α) is) α') (K.id c))) := by
  rw [← K.assoc, act_seq]
  simp only [first_exchange L]
  rw [← act_seq, K.assoc, ← K.assoc (act S Z (fun i => T.map (ds i).α (K.id c)) is),
    gather_outer N, K.assoc, ← T.map_seq, K.id_seq]
end ContextualComposition.NativeFinitePush.DependentFibre
