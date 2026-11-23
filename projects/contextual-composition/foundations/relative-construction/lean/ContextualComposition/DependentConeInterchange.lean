module

public import ContextualComposition.ConeWiring
public import Mathlib.CategoryTheory.Monad.Basic

/-! Dependent serial interchange for cones of supplied effect contexts. The second native map is indexed by the full first joint witness and targets the continuation at its projected witness. -/

@[expose] public section

namespace ContextualComposition.DependentConeInterchange

open CategoryTheory CouplingPullbacks AllCouplings CouplingChains ConeWiring
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (T : CategoryTheory.Monad (Type u))
variable {X Y Z A B : Type u}

def ret (x : X) : T.obj X := T.η.app X x
def bind (p : T.obj X) (k : X → T.obj Y) : T.obj Y := T.μ.app Y (push T.toFunctor k p)

theorem bind_push (p : T.obj X) (f : X → Y) (k : Y → T.obj Z) :
    bind T (push T.toFunctor f p) k = bind T p (k ∘ f) :=
  congrArg (T.μ.app Z) (push_push T.toFunctor f k p)

theorem push_bind (p : T.obj X) (k : X → T.obj Y) (f : Y → Z) :
    push T.toFunctor f (bind T p k) = bind T p (fun x => push T.toFunctor f (k x)) := by
  let h := T.μ.naturality (TypeCat.ofHom f)
  exact (congrArg (fun (e : T.obj (T.obj Y) ⟶ T.obj Z) => e (push T.toFunctor k p)) h).symm.trans
    (congrArg (T.μ.app Z) (push_push T.toFunctor k (push T.toFunctor f) p))

theorem ret_bind (x : X) (k : X → T.obj Y) : bind T (ret T x) k = k x := by
  have eq := congrArg (fun (h : X ⟶ T.obj (T.obj Y)) => h x) (T.η.naturality (TypeCat.ofHom k))
  exact (congrArg (T.μ.app Y) eq.symm).trans (congrArg (fun (h : T.obj Y ⟶ T.obj Y) => h (k x)) (T.left_unit Y))

theorem push_ret (x : X) (f : X → Y) : push T.toFunctor f (ret T x) = ret T (f x) :=
  (congrArg (fun (h : X ⟶ T.obj Y) => h x) (T.η.naturality (TypeCat.ofHom f))).symm

theorem bind_ret (p : T.obj X) : bind T p (ret T) = p :=
  congrArg (fun (h : T.obj X ⟶ T.obj X) => h p) (T.right_unit X)

theorem bind_assoc (p : T.obj X) (k : X → T.obj Y) (l : Y → T.obj Z) :
    bind T (bind T p k) l = bind T p (fun x => bind T (k x) l) := by
  change T.μ.app Z (push T.toFunctor l (bind T p k)) = _
  rw [push_bind]
  let c := fun x => push T.toFunctor l (k x)
  have e := congrArg (fun (h : T.obj (T.obj (T.obj Z)) ⟶ T.obj Z) => h (push T.toFunctor c p)) (T.assoc Z)
  exact e.symm.trans (congrArg (T.μ.app Z) (push_push T.toFunctor c (T.μ.app Z) p))

abbrev Ctx := Context T.toFunctor
abbrev Total (P : Ctx T A) := Σ a, (P a).carrier
def totalMap {P Q : Ctx T A} (u : P ⟶ Q) (z : Total T P) : Total T Q := ⟨z.1,(u z.1).run z.2⟩

def star (P : Ctx T A) (R : Ctx T (Total T P)) : Ctx T A :=
  fun a => ⟨Σ z : (P a).carrier, (R ⟨a,z⟩).carrier,
    bind T (P a).law (fun z => push T.toFunctor (Sigma.mk z) (R ⟨a,z⟩).law)⟩

/-- A conditional native map with the exact dependence on the projected first input. -/
abbrev Conditional {P Q : Ctx T A} (u : P ⟶ Q) (R : Ctx T (Total T P)) (S : Ctx T (Total T Q)) :=
  ∀ z, StateMap T.toFunctor (R z) (S (totalMap T u z))

variable {P Q L : Ctx T A} {R : Ctx T (Total T P)} {S : Ctx T (Total T Q)} {N : Ctx T (Total T L)}

def assemble (u : P ⟶ Q) (v : Conditional T u R S) : star T P R ⟶ star T Q S := fun a => {
  run := fun t => ⟨(u a).run t.1,(v ⟨a,t.1⟩).run t.2⟩
  preserves := by
    change push T.toFunctor _ (bind T _ _) = bind T _ _
    rw [push_bind, ← (u a).preserves, bind_push]
    apply congrArg (bind T (P a).law)
    funext z
    rw [push_push]
    let incl (y : (S ⟨a,(u a).run z⟩).carrier) : (star T Q S a).carrier := ⟨(u a).run z,y⟩
    exact (push_push T.toFunctor (v ⟨a,z⟩).run incl (R ⟨a,z⟩).law).symm.trans
      (congrArg (push T.toFunctor incl) (v ⟨a,z⟩).preserves) }

def composeConditional (u : P ⟶ Q) (v : Conditional T u R S) (t : Q ⟶ L) (s : Conditional T t S N) :
    Conditional T (u ≫ t) R N := fun z =>
  (show R z ⟶ S (totalMap T u z) from v z) ≫ (show S (totalMap T u z) ⟶ N (totalMap T (u ≫ t) z) from s _)

/-- Both routes preserve the full raw pair and use the second map at the actual projected first witness. -/
theorem interchange (u : P ⟶ Q) (v : Conditional T u R S) (t : Q ⟶ L) (s : Conditional T t S N) :
    assemble T u v ≫ assemble T t s = assemble T (u ≫ t) (composeConditional T u v t s) := rfl

theorem extension_interchange (u : P ⟶ Q) (v : Conditional T u R S) (t : Q ⟶ L) (s : Conditional T t S N) :
    totalMap T (assemble T t s) ∘ totalMap T (assemble T u v) =
    totalMap T (assemble T (u ≫ t) (composeConditional T u v t s)) := rfl

def assembleCone {I : Type*} {Q : I → Ctx T A} {S : ∀ i, Ctx T (Total T (Q i))}
    (u : Wiring P Q) (v : ∀ i, Conditional T (u i) R (S i)) :
    Wiring (star T P R) (fun i => star T (Q i) (S i)) := fun i => assemble T (u i) (v i)

theorem cone_substitution {I : Type*} {J : I → Type*} {Q : I → Ctx T A} {S : ∀ i, Ctx T (Total T (Q i))}
    {L : ∀ i, J i → Ctx T A} {N : ∀ i j, Ctx T (Total T (L i j))}
    (u : Wiring P Q) (v : ∀ i, Conditional T (u i) R (S i))
    (t : ∀ i, Wiring (Q i) (L i)) (s : ∀ i j, Conditional T (t i j) (S i) (N i j)) (i j) :
    ConeWiring.subst (assembleCone T u v) (fun i => assembleCone T (t i) (s i)) ⟨i,j⟩ =
      assemble T (ConeWiring.subst u t ⟨i,j⟩) (composeConditional T (u i) (v i) (t i j) (s i j)) := rfl

def pullTotal (f : B → A) (P : Ctx T A) (x : Total T (P ∘ f)) : Total T P := ⟨f x.1,x.2⟩

theorem reindex_star (f : B → A) (P : Ctx T A) (R : Ctx T (Total T P)) :
    (star T P R) ∘ f = star T (P ∘ f) (R ∘ pullTotal T f P) := rfl

theorem reindex_assemble (f : B → A) (u : P ⟶ Q) (v : Conditional T u R S) :
    (ConeWiring.reindex T.toFunctor f).map (assemble T u v) =
    assemble T (R := R ∘ pullTotal T f P) (S := S ∘ pullTotal T f Q)
      ((ConeWiring.reindex T.toFunctor f).map u) (fun z => v (pullTotal T f P z)) := rfl

def unit (A : Type u) : Ctx T A := fun _ => ⟨PUnit,ret T PUnit.unit⟩

/-- The singleton coordinates removed by the unitors are actual raw coordinates. -/
def leftUnit (P : Ctx T A) (a : A) :
    StateIso T.toFunctor (star T (unit T A) (fun z => P z.1) a) (P a) where
  equiv := { toFun := fun x => x.2, invFun := fun x => ⟨⟨⟩,x⟩, left_inv := fun ⟨⟨⟩,_⟩ => rfl, right_inv := fun _ => rfl }
  preserves := by
    change push T.toFunctor _ (bind T (ret T PUnit.unit) _) = _
    rw [ret_bind,push_push]
    exact push_id T.toFunctor _

def rightUnit (P : Ctx T A) (a : A) :
    StateIso T.toFunctor (star T P (unit T (Total T P)) a) (P a) where
  equiv := { toFun := Sigma.fst, invFun := fun x => ⟨x,⟨⟩⟩, left_inv := fun ⟨_,⟨⟩⟩ => rfl, right_inv := fun _ => rfl }
  preserves := by
    change push T.toFunctor _ (bind T (P a).law (fun z => push T.toFunctor _ (ret T PUnit.unit))) = _
    rw [push_bind]
    apply Eq.trans _ (bind_ret T (P a).law)
    apply congrArg (bind T (P a).law)
    funext z
    exact (push_push T.toFunctor _ _ _).trans (push_ret T _ _)

variable (P R) (K : Ctx T (Total T (star T P R)))

def tripleInput (z : Total T R) : Total T (star T P R) := ⟨z.1.1,⟨z.1.2,z.2⟩⟩

def associate (a : A) :
    StateIso T.toFunctor (star T (star T P R) K a) (star T P (star T R (K ∘ tripleInput T P R)) a) where
  equiv := {
    toFun := fun z => ⟨z.1.1,⟨z.1.2,z.2⟩⟩
    invFun := fun z => ⟨⟨z.1,z.2.1⟩,z.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  preserves := by
    change push T.toFunctor _ (bind T (bind T _ _) _) = bind T _ _
    rw [push_bind,bind_assoc]
    apply congrArg (bind T (P a).law)
    funext z
    change bind T (push T.toFunctor (Sigma.mk (β := fun y => (R ⟨a,y⟩).carrier) z) (R ⟨a,z⟩).law) _ = push T.toFunctor _ (bind T _ _)
    rw [bind_push,push_bind]
    apply congrArg (bind T (R ⟨a,z⟩).law)
    funext r
    change push T.toFunctor _ (push T.toFunctor _ _) = push T.toFunctor _ (push T.toFunctor _ _)
    rw [push_push,push_push]
    rfl

variable {P R} {K K' : Ctx T (Total T (star T P R))}

private theorem state_ext {U V : Effect T.toFunctor} {p q : StateMap T.toFunctor U V} (h : p.run = q.run) : p = q := by
  cases p; cases q; cases h; rfl

/-- Naturality in both levels: native triangles for each constituent give a triangle for every assembled projection. -/
theorem assembled_triangle {Z' : Ctx T A} {R' : Ctx T (Total T Z')} (a : P ⟶ Z') (b : Conditional T a R R')
    (u : P ⟶ Q) (v : Conditional T u R S) (u' : Z' ⟶ Q) (v' : Conditional T u' R' S)
    (hu : ∀ i z, (u i).run z = (u' i).run ((a i).run z))
    (hv : ∀ i z r, (v ⟨i,z⟩).run r ≍ (v' ⟨i,(a i).run z⟩).run ((b ⟨i,z⟩).run r)) :
    assemble T u v = assemble T a b ≫ assemble T u' v' := by
  funext i
  have eq : (assemble T u v i).run = ((assemble T a b ≫ assemble T u' v') i).run := by
    funext t
    exact Sigma.ext (hu i t.1) (hv i t.1 t.2)
  exact state_ext T eq

def assocMap (P : Ctx T A) (R : Ctx T (Total T P)) (K : Ctx T (Total T (star T P R))) :
    star T (star T P R) K ⟶ star T P (star T R (K ∘ tripleInput T P R)) :=
  fun a => (associate T P R K a).forward T.toFunctor

def inside (u : P ⟶ Q) (v : Conditional T u R S) {H : Ctx T (Total T (star T Q S))}
    (w : Conditional T (assemble T u v) K H) :
    Conditional T u (star T R (K ∘ tripleInput T P R)) (star T S (H ∘ tripleInput T Q S)) :=
  fun z => assemble T (P := R) (Q := S ∘ totalMap T u) (R := K ∘ tripleInput T P R)
    (S := fun t => H ⟨t.1.1,⟨(u t.1.1).run t.1.2,t.2⟩⟩) v (fun t => w (tripleInput T P R t)) z

theorem associate_natural (u : P ⟶ Q) (v : Conditional T u R S) {H : Ctx T (Total T (star T Q S))}
    (w : Conditional T (assemble T u v) K H) :
    assemble T (assemble T u v) w ≫ assocMap T Q S H =
      assocMap T P R K ≫ assemble T u (inside T u v w) := rfl

def unitMap {A : Type u} : unit T A ⟶ unit T A := 𝟙 _

theorem leftUnit_natural (u : P ⟶ Q) (a : A) :
    TypeCat.ofHom (assemble T (R := fun z => P z.1) (S := fun z => Q z.1) (unitMap T) (fun z => u z.1) a).run ≫
      TypeCat.ofHom (leftUnit T Q a).equiv =
    TypeCat.ofHom (leftUnit T P a).equiv ≫ TypeCat.ofHom (u a).run := rfl

theorem rightUnit_natural (u : P ⟶ Q) (a : A) :
    TypeCat.ofHom (assemble T (R := unit T _) (S := unit T _) u (fun _ => ⟨id,push_id T.toFunctor _⟩) a).run ≫
      TypeCat.ofHom (rightUnit T Q a).equiv =
    TypeCat.ofHom (rightUnit T P a).equiv ≫ TypeCat.ofHom (u a).run := rfl

end ContextualComposition.DependentConeInterchange
