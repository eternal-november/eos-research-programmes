import ContextualComposition.AccumulationAlgebra
open CategoryTheory CategoryTheory.Functor Opposite ContextualComposition.GrothendieckStep PackedFree AccumulationAlgebra
namespace ReviewerArbitrary
universe b w u v
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,max u v} B} (S : P.Split)
-- No assumption that K is in the image or a free algebra.
theorem fork (K : (monad S).Algebra) : cons S K.A ≫ K.a = (step S).map K.a ≫ restrict S K := by
  have h := congrArg (inc S ((free S).obj K.A) 1 ≫ ·) K.assoc
  change inc S ((free S).obj K.A) 1 ≫ join S K.A ≫ K.a =
    inc S ((free S).obj K.A) 1 ≫ (free S).map K.a ≫ K.a at h
  erw [← Category.assoc,singleton_join,← Category.assoc,inc_map,Category.assoc] at h
  exact h
theorem rows (K : (monad S).Algebra) (n : Nat) :
    inc S K.A n ≫ K.a = foldLayer S (restrict S K) (𝟙 K.A) n := by
  induction n with
  | zero => exact K.unit
  | succ n ih =>
    rw [← inc_cons S K.A n,Category.assoc,fork,← Category.assoc,← Functor.map_comp,ih]
    rfl
theorem inverseOnAny (K : (monad S).Algebra) : ((extend S).obj ((readOne S).obj K)).a = K.a := by
  apply pack_ext; intro n
  exact (inc_fold S _ _ n).trans (rows S K n).symm
theorem iffOnAny (K L : (monad S).Algebra) (h : K.A ⟶ L.A) :
    ((step S).map h ≫ restrict S L = restrict S K ≫ h) ↔ ((free S).map h ≫ L.a = K.a ≫ h) := by
  constructor
  · intro p
    have q := (strictMap S (restrict S K) (restrict S L) h).mp p.symm
    exact (congrArg ((free S).map h ≫ ·) (inverseOnAny S L).symm).trans
      (q.trans (congrArg (· ≫ h) (inverseOnAny S K)))
  · intro q
    exact ((readOne S).map (⟨h,q⟩ : K ⟶ L)).h
example (K L M : (monad S).Algebra) (f : K ⟶ L) (g : L ⟶ M) :
    ((extend S).map ((readOne S).map (f ≫ g))).f = f.f ≫ g.f := rfl
end ReviewerArbitrary
