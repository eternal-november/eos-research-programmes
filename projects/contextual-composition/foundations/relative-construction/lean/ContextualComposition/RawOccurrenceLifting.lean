module
public import ContextualComposition.GuardedOccurrencePrefixes

/-! Raw lift from a specified initial state under surjectivity at its reachable joint states. The constructed inverse sequence has no asserted infinite effect. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.RawOccurrenceLifting
open CategoryTheory JointOccurrenceAdmission JointOccurrenceSystem GuardedOccurrencePrefixes
set_option backward.isDefEq.respectTransparency false
universe u
variable {T : CategoryTheory.Monad (Type u)} {S P : Polynomial.{u}} {X Y : Type u}
variable {A : System T.toFunctor S X} {B : System T.toFunctor S Y} {h : X → Y}

inductive Reachable (A : System T.toFunctor S X) (x : X) : X → Prop where
  | root : Reachable A x x
  | child {y} : Reachable A x y → (w : A.witness y) → (i : S.Pos (A.output y w).1) →
      Reachable A x ((A.output y w).2 i)

theorem frontier_reachable [Finitary S] (A : System T.toFunctor S X) (x : X) (n : Nat)
    (t : (prefixes A x n).raw) (i : (power S n).Pos ((prefixes A x n).frontier t).1) :
    Reachable A x (((prefixes A x n).frontier t).2 i) := by
  induction n with
  | zero => exact .root
  | succ n ih => exact .child (ih t.1 i.1) (t.2 i.1) i.2

theorem assignments_onto (f : NativeMap A B h) (q : Body P X) {q' : Body P Y} (e : map P h q = q')
    (sur : ∀ i, Function.Surjective (f.onWitness (q.2 i))) : Function.Surjective (assignmentMap f q e) := by
  subst q'
  intro w
  exact ⟨fun i => (sur i (w i)).choose,funext fun i => (sur i (w i)).choose_spec⟩

theorem extend_lift [Finitary S] (f : NativeMap A B h) (x : X)
    (sur : ∀ y, Reachable A x y → Function.Surjective (f.onWitness y))
    (n : Nat) (t : (prefixes A x n).raw) (z : (prefixes B (h x) (n+1)).raw)
    (matchPrefix : (prefixMap f x n).run t = forgetLast B (h x) n z) :
    ∃ r, forgetLast A x n r = t ∧ (prefixMap f x (n+1)).run r = z := by
  obtain ⟨z,w⟩ := z
  change (prefixMap f x n).run t = z at matchPrefix
  subst z
  obtain ⟨l,hl⟩ := assignments_onto f _ ((prefixMap f x n).body t)
    (fun i => sur _ (frontier_reachable A x n t i)) w
  exact ⟨⟨t,l⟩,rfl,congrArg (Sigma.mk ((prefixMap f x n).run t)) hl⟩

structure RawLimit [Finitary S] (A : System T.toFunctor S X) (x : X) where
  stage : ∀ n, (prefixes A x n).raw
  trunc : ∀ n, forgetLast A x n (stage (n+1)) = stage n

def mapLimit [Finitary S] (f : NativeMap A B h) (x : X) (q : RawLimit A x) : RawLimit B (h x) where
  stage n := (prefixMap f x n).run (q.stage n)
  trunc n := (truncate_map f x n _).symm.trans (congrArg (prefixMap f x n).run (q.trunc n))

private def chooseNext [Finitary S] (f : NativeMap A B h) (x : X)
    (sur : ∀ y, Reachable A x y → Function.Surjective (f.onWitness y)) (q : RawLimit B (h x))
    (n : Nat) (t : {r // (prefixMap f x n).run r = q.stage n}) :
    {r // forgetLast A x n r = t.val ∧ (prefixMap f x (n+1)).run r = q.stage (n+1)} :=
  let lift := extend_lift f x sur n t.val (q.stage (n+1)) (t.property.trans (q.trunc n).symm)
  ⟨lift.choose,lift.choose_spec⟩

private def lifts [Finitary S] (f : NativeMap A B h) (x : X)
    (sur : ∀ y, Reachable A x y → Function.Surjective (f.onWitness y)) (q : RawLimit B (h x)) :
    (n : Nat) → {r // (prefixMap f x n).run r = q.stage n}
  | 0 => ⟨PUnit.unit,Subsingleton.elim (PUnit.unit : PUnit.{u+1}) (q.stage 0)⟩
  | n+1 => let z := chooseNext f x sur q n (lifts f x sur q n); ⟨z.val,z.property.2⟩

theorem raw_limit_surjective [Finitary S] (f : NativeMap A B h) (x : X)
    (sur : ∀ y, Reachable A x y → Function.Surjective (f.onWitness y)) : Function.Surjective (mapLimit f x) := by
  intro q
  let selected := lifts f x sur q
  refine ⟨⟨fun n => (selected n).val,fun n => (chooseNext f x sur q n (selected n)).property.1⟩,?_⟩
  have ext (u v : RawLimit B (h x)) (e : u.stage = v.stage) : u = v := by
    cases u; cases v; cases e; rfl
  exact ext _ _ (funext fun n => (selected n).property)

end ContextualComposition.RawOccurrenceLifting
