module
public import ContextualComposition.GrothendieckIterates
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares
open CategoryTheory Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] (P : Endpoints.{b,w,u,v} B)
/-- Grade chains without any terminal payload. -/
inductive Chain : Nat → B → Type (max b u)
  | nil (A : B) : Chain 0 A
  | cons {A n} (p : P.grades.obj (op A)) (t : Chain n ((P.extend A).obj p)) : Chain (n+1) A

variable {P}
def endpoint : {n : Nat} → {A : B} → Chain P n A → B
  | _, A, .nil _ => A
  | _, _, .cons _ t => endpoint t

def next {A D : B} (u : A ⟶ D) {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    (k : p ⟶ (P.grades.map u.op).toFunctor.obj q) :
    (P.extend A).obj p ⟶ (P.extend D).obj q := (P.extend A).map k ≫ (P.lift u).app q

/-- An independent chain square over a specified base arrow. It has no payload component. -/
def Square : {n : Nat} → {A D : B} → (u : A ⟶ D) → Chain P n A → Chain P n D → Type (max u v)
  | 0, _, _, _, .nil _, .nil _ => PUnit
  | _+1, _, _, u, .cons p t, .cons q z =>
      Σ k : p ⟶ (P.grades.map u.op).toFunctor.obj q, Square (next u k) t z

def terminalMap : {n : Nat} → {A D : B} → {u : A ⟶ D} → {t : Chain P n A} →
    {z : Chain P n D} → Square u t z → (endpoint t ⟶ endpoint z)
  | 0, _, _, u, .nil _, .nil _, _ => u
  | n+1, _, _, u, .cons _ t, .cons _ z, h => @terminalMap n _ _ (next u h.1) t z h.2

variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
def DecoratedHom {n : Nat} {A D : B} (u : A ⟶ D) (t : Chain P n A) (z : Chain P n D)
    (x : Y.obj (op (endpoint t))) (y : Y.obj (op (endpoint z))) :=
  Σ s : Square u t z, x ⟶ (Y.map (terminalMap s).op).toFunctor.obj y

variable (S : P.Split)
def realize : {n : Nat} → {A : B} → (t : Chain P n A) → Y.obj (op (endpoint t)) →
    (Iterates.layer P S Y n).obj (op A)
  | 0, _, .nil _, x => x
  | _+1, _, .cons p t, x => pair _ _ p (realize t x)

def unrealize : (n : Nat) → (A : B) → (Iterates.layer P S Y n).obj (op A) →
    Σ t : Chain P n A, Y.obj (op (endpoint t))
  | 0, A, x => ⟨.nil A,x⟩
  | n+1, A, z =>
    let t := unrealize n _ (payload _ (P.extend A) z)
    ⟨.cons (grade _ _ z) t.1,t.2⟩

theorem unpack_pack {n A} (t : Chain P n A) (x : Y.obj (op (endpoint t))) :
    unrealize Y S n A (realize Y S t x) = ⟨t,x⟩ := by
  induction t with
  | nil => rfl
  | @cons A n p t ih =>
    exact congrArg (fun a : Σ t : Chain P n ((P.extend A).obj p), Y.obj (op (endpoint t)) =>
      (⟨Chain.cons p a.1,a.2⟩ : Σ t : Chain P (n+1) A, Y.obj (op (endpoint t)))) (ih x)

theorem pack_unpack (n : Nat) (A : B) (z : (Iterates.layer P S Y n).obj (op A)) :
    realize Y S (unrealize Y S n A z).1 (unrealize Y S n A z).2 = z := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    exact congrArg (pair _ (P.extend A) (grade _ _ z)) (ih _ (payload _ _ z))

def realizedEquiv (n : Nat) (A : B) :
    (Σ t : Chain P n A, Y.obj (op (endpoint t))) ≃ (Iterates.layer P S Y n).obj (op A) where
  toFun z := realize Y S z.1 z.2
  invFun := unrealize Y S n A
  left_inv z := unpack_pack Y S z.1 z.2
  right_inv := pack_unpack Y S n A

def splitDec {n A D} (u : A ⟶ D) (p : P.grades.obj (op A)) (q : P.grades.obj (op D))
    (t : Chain P n ((P.extend A).obj p)) (z : Chain P n ((P.extend D).obj q))
    (x : Y.obj (op (endpoint t))) (y : Y.obj (op (endpoint z))) :
    DecoratedHom Y u (.cons p t) (.cons q z) x y ≃
      Σ k : p ⟶ (P.grades.map u.op).toFunctor.obj q, DecoratedHom Y (next u k) t z x y where
  toFun f := ⟨f.1.1,f.1.2,f.2⟩
  invFun f := ⟨⟨f.1,f.2.1⟩,f.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tailTarget {n A D} (u : A ⟶ D) {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    (k : p ⟶ (P.grades.map u.op).toFunctor.obj q) (z : (Iterates.layer P S Y n).obj (op ((P.extend D).obj q))) :
    ((Iterates.layer P S Y n).map (next u k).op).toFunctor.obj z =
      ((Iterates.layer P S Y n).map ((P.extend A).map k).op).toFunctor.obj
        (((Iterates.layer P S Y n).map ((P.lift u).app q).op).toFunctor.obj z) := by
  rw [next,op_comp,Functor.map_comp]; rfl

/-- Each independent grade square plus final payload arrow is exactly a nested
native arrow into the reindexed target, for any (not necessarily invertible) base map. -/
def squareEquiv : {n : Nat} → {A D : B} → (u : A ⟶ D) → (t : Chain P n A) → (z : Chain P n D) →
    (x : Y.obj (op (endpoint t))) → (y : Y.obj (op (endpoint z))) →
    DecoratedHom Y u t z x y ≃
      (realize Y S t x ⟶ ((Iterates.layer P S Y n).map u.op).toFunctor.obj (realize Y S z y))
  | 0, _, _, _, .nil _, .nil _, _, _ => {
      toFun := fun f => f.2
      invFun := fun h => ⟨PUnit.unit,h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | n+1, A, _, u, .cons p t, .cons q z, x, y =>
    (splitDec Y u p q t z x y).trans ((Equiv.sigmaCongrRight fun k =>
      (squareEquiv (next u k) t z x y).trans
        (Equiv.cast (congrArg (fun dest => (realize Y S t x ⟶ dest))
          (tailTarget Y S u k (realize Y S z y))))).trans (homEquiv (Y := Iterates.layer P S Y n) (e := P.extend A) (realize Y S (.cons p t) x) (((Iterates.layer P S Y (n+1)).map u.op).toFunctor.obj (realize Y S (.cons q z) y))).symm)

def verticalEquiv {n A} (t z : Chain P n A)
    (x : Y.obj (op (endpoint t))) (y : Y.obj (op (endpoint z))) :
    DecoratedHom Y (𝟙 A) t z x y ≃ (realize Y S t x ⟶ realize Y S z y) :=
  (squareEquiv Y S (𝟙 A) t z x y).trans (Equiv.cast (congrArg (fun dest => (realize Y S t x ⟶ dest))
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor ((Iterates.layer P S Y n).map_id (op A)))
      (realize Y S z y))))

namespace Example
open Families
def src : Chain endpoints 2 Unit := .cons (fun _ => Unit) (.cons (fun _ => Unit) (.nil _))
def dst : Chain endpoints 2 Bool := .cons wideGrade
  (.cons (fun z => if (show Bool from z.2) = true then Bool else Empty) (.nil _))

def sq (b : Bool) : Square (selectPoint b) src dst :=
  ⟨fun _ => TypeCat.ofHom (fun _ => true),fun _ => TypeCat.ofHom (fun _ => false),PUnit.unit⟩

theorem terminal_test (b : Bool) :
    (terminalMap (t := src) (z := dst) (u := selectPoint b) (sq b)) ⟨⟨(),()⟩,()⟩ =
      ⟨⟨b,true⟩,false⟩ := rfl
end Example
end ContextualComposition.GrothendieckStep.TelescopeSquares
