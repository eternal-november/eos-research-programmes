module
public import ContextualComposition.SpanApex
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares.Snoc
open CategoryTheory Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B}

def append : {n : Nat} → {A : B} → (t : Chain P n A) → P.grades.obj (op (endpoint t)) → Chain P (n+1) A
  | 0, _, .nil _, x => .cons x (.nil _)
  | _+1, _, .cons p t, x => .cons p (append t x)

def cut : {n : Nat} → {A : B} → Chain P (n+1) A → Σ t : Chain P n A, P.grades.obj (op (endpoint t))
  | 0, _, .cons p (.nil _) => ⟨.nil _, p⟩
  | n+1, _, .cons p z => let h := @cut n _ z; ⟨.cons p h.1,h.2⟩

theorem cut_append : {n : Nat} → {A : B} → (t : Chain P n A) → (x : P.grades.obj (op (endpoint t))) →
    cut (append t x) = ⟨t,x⟩
  | 0, _, .nil _, _ => rfl
  | _+1, _, .cons p t, x => congrArg (fun h => (⟨Chain.cons p h.1,h.2⟩ : Σ t : Chain P _ _, P.grades.obj (op (endpoint t)))) (cut_append t x)

theorem append_cut : {n : Nat} → {A : B} → (t : Chain P (n+1) A) → append (cut t).1 (cut t).2 = t
  | 0, _, .cons p (.nil _) => rfl
  | n+1, _, .cons p t => congrArg (Chain.cons p) (@append_cut n _ t)

def objects (n : Nat) (A : B) : (Σ t : Chain P n A, P.grades.obj (op (endpoint t))) ≃ Chain P (n+1) A :=
  ⟨fun h => append h.1 h.2,cut,fun h => cut_append h.1 h.2,append_cut⟩

def squares : {n : Nat} → {A D : B} → (a : A ⟶ D) → (t : Chain P n A) → (z : Chain P n D) →
    (x : P.grades.obj (op (endpoint t))) → (y : P.grades.obj (op (endpoint z))) →
    DecoratedHom P.grades a t z x y ≃ Square a (append t x) (append z y)
  | 0, _, _, _, .nil _, .nil _, _, _ =>
    ⟨fun f => ⟨f.2,PUnit.unit⟩,fun g => ⟨PUnit.unit,g.1⟩,fun _ => rfl,fun _ => rfl⟩
  | n+1, _, _, a, .cons p t, .cons q z, x, y =>
    (splitDec P.grades a p q t z x y).trans
      (Equiv.sigmaCongrRight (fun k => @squares n _ _ (next a k) t z x y))

theorem endpoint_append : {n : Nat} → {A : B} → (t : Chain P n A) → (x : P.grades.obj (op (endpoint t))) →
    endpoint (append t x) = (P.extend (endpoint t)).obj x
  | 0, _, .nil _, _ => rfl
  | _+1, _, .cons _ t, x => endpoint_append t x

theorem terminal_append : {n : Nat} → {A D : B} → (a : A ⟶ D) → (t : Chain P n A) → (z : Chain P n D) →
    (x : P.grades.obj (op (endpoint t))) → (y : P.grades.obj (op (endpoint z))) →
    (f : DecoratedHom P.grades a t z x y) →
    HEq (terminalMap (t := append t x) (z := append z y) (u := a) (squares a t z x y f)) (next (terminalMap f.1) f.2)
  | 0, _, _, _, .nil _, .nil _, _, _, _ => HEq.rfl
  | n+1, _, _, a, .cons _ t, .cons _ z, x, y, f =>
    @terminal_append n _ _ (next a f.1.1) t z x y ⟨f.1.2,f.2⟩
end ContextualComposition.GrothendieckStep.TelescopeSquares.Snoc

namespace ContextualComposition.GrothendieckStep.SpanApex
open CategoryTheory Opposite TelescopeSquares
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (S : P.Split)

private theorem rebase_head {A D : B} {a b : A ⟶ D} (h : a = b)
    {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    {n} {t : Chain P n _} {z : Chain P n _} (s : Square a (.cons p t) (.cons q z)) :
    HEq (rebaseSquare (t := .cons p t) (z := .cons q z) h s).1 s.1 := by subst b; rfl

private theorem comp_transport {C : Type*} [Category* C] {x y z z' : C} (f : x ⟶ y) (g : y ⟶ z) (h : z = z') :
    HEq (f ≫ g ≫ eqToHom h) (f ≫ g) := by subst z'; simp

private theorem fiber_id {K : Type*} [Category* K] {e : K ⥤ B} (x : Total P.grades e) :
    HEq (payloadMap (𝟙 x)) (𝟙 (payload P.grades e x)) := by
  change HEq ((Grothendieck.Hom.fiber (𝟙 x.unop)).unop) _
  rw [Grothendieck.id_fiber]
  refine HEq.trans (heq_of_eq (eqToHom_unop (C := (P.grades.obj (op (e.obj (grade _ _ x))) : Type _)) _)) ?_
  exact eqToHom_heq_id_dom _ _ _

private theorem head_heq {A : B} (p : P.grades.obj (op A)) : HEq (headId (P := P) p) (𝟙 p) :=
  eqToHom_heq_id_dom _ _ _

theorem chainHoms_id {A : B} (t : Chain P 2 A) :
    ((chainHoms P S (𝟙 A) t t) (squareId S t)).1 = 𝟙 (chainPair P S t) := by
  cases t with | cons p t =>
   cases t with | cons q t =>
    cases t
    apply (homEquiv _ _).injective
    apply Sigma.ext
    · apply (homEquiv _ _).injective
      refine Sigma.ext (by rfl) ?_
      exact (head_heq (P := P) p).trans (fiber_id (P := P) (e := 𝟭 B) (pair _ _ A p)).symm
    · change HEq (rebaseSquare (t := .cons q (.nil _)) (z := .cons q (.nil _)) (next_id S p).symm (squareId S (.cons q (.nil _)))).1 (payloadMap (𝟙 _))
      refine (rebase_head _ _).trans ?_
      exact (head_heq (P := P) q).trans (fiber_id (P := P) (e := right P S) (pair _ _ (pair P.grades (𝟭 B) A p) q)).symm

theorem chainHoms_comp {A D E : B} {a : A ⟶ D} {b : D ⟶ E} (t : Chain P 2 A) (z : Chain P 2 D) (w : Chain P 2 E)
    (f : Square a t z) (g : Square b z w) :
    ((chainHoms P S (a ≫ b) t w) (squareComp S f g)).1 =
      ((chainHoms P S a t z) f).1 ≫ ((chainHoms P S b z w) g).1 := by
  cases t with | cons p t =>
   cases t with | cons q t =>
    cases t
    cases z with | cons r z =>
     cases z with | cons s z =>
      cases z
      cases w with | cons l w =>
       cases w with | cons m w =>
        cases w
        apply (homEquiv _ _).injective
        apply Sigma.ext
        · apply (homEquiv _ _).injective
          refine Sigma.ext (by rfl) ?_
          apply heq_of_eq
          symm
          exact payload_comp _ _
        · change HEq (rebaseSquare (t := .cons q (.nil _)) (z := .cons m (.nil _)) (next_comp S f.1 g.1).symm (squareComp S f.2 g.2)).1 (payloadMap (_ ≫ _))
          refine (rebase_head _ _).trans ?_
          rw [payload_comp]
          change HEq (headComp (P := P) f.2.1 g.2.1) _
          exact (comp_transport _ _ _).trans (comp_transport _ _ _).symm
end ContextualComposition.GrothendieckStep.SpanApex

namespace ContextualComposition.GrothendieckStep.SpanApex
open CategoryTheory Opposite TelescopeSquares
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (S : P.Split)

abbrev Points (n : Nat) := Σ A : B, Chain P n A

def lastPoint (n : Nat) :
    (Σ h : Points (P := P) n, P.grades.obj (op (endpoint h.2))) ≃ Points (P := P) (n+1) where
  toFun h := ⟨h.1.1,Snoc.append h.1.2 h.2⟩
  invFun h := ⟨⟨h.1,(Snoc.cut h.2).1⟩,(Snoc.cut h.2).2⟩
  left_inv h := congrArg (fun j => (⟨⟨h.1.1,j.1⟩,j.2⟩ : Σ k : Points (P := P) n, P.grades.obj (op (endpoint k.2)))) (Snoc.cut_append h.1.2 h.2)
  right_inv h := congrArg (Sigma.mk h.1) (Snoc.append_cut h.2)

def totalPoints {K : Type*} [Category* K] (e : K ⥤ B) :
    (Σ k : K, P.grades.obj (op (e.obj k))) ≃ Total P.grades e :=
  ⟨fun j => pair _ _ j.1 j.2,fun k => ⟨grade _ _ k,payload _ _ k⟩,fun _ => rfl,fun _ => rfl⟩

structure PointModel (n : Nat) (V : TwoLegs.{b,w,u,v} B) where
  decode : V.apex ≃ Points (P := P) n
  source_eq (k : V.apex) : (decode k).1 = V.source.obj k
  dest_eq (k : V.apex) : endpoint (decode k).2 = V.dest.obj k

def gradeCast {A D : B} (h : A = D) : (P.grades.obj (op A) : Type _) ≃ P.grades.obj (op D) := by subst D; exact Equiv.refl _

theorem extendCast {A D : B} (h : A = D) (p : P.grades.obj (op A)) :
    (P.extend D).obj (gradeCast h p) = (P.extend A).obj p := by subst D; rfl

def pointStepDecode {n : Nat} {V : TwoLegs.{b,w,u,v} B} (m : PointModel (P := P) n V) :
    (append P S V).apex ≃ Points (P := P) (n+1) :=
  (totalPoints V.dest).symm.trans ((Equiv.sigmaCongr (β₁ := fun k => (P.grades.obj (op (V.dest.obj k)) : Type _)) (β₂ := fun k => (P.grades.obj (op (endpoint k.2)) : Type _)) m.decode (fun k => gradeCast (P := P) (m.dest_eq k).symm)).trans (lastPoint n))

def pointStep {n : Nat} {V : TwoLegs.{b,w,u,v} B} (m : PointModel (P := P) n V) :
    PointModel (P := P) (n+1) (append P S V) where
  decode := pointStepDecode S m
  source_eq k := m.source_eq (grade _ _ k)
  dest_eq k := (Snoc.endpoint_append (m.decode (grade _ _ k)).2 (gradeCast (P := P) (m.dest_eq (grade _ _ k)).symm (payload _ _ k))).trans (extendCast (m.dest_eq (grade _ _ k)).symm (payload _ _ k))

def primitivePoints : PointModel (P := P) 1 (primitive P S) where
  decode :=
    { toFun := fun k => ⟨grade _ _ k,.cons (payload _ _ k) (.nil _)⟩
      invFun := fun ⟨A,.cons p (.nil _)⟩ => pair _ _ A p
      left_inv := fun _ => rfl
      right_inv := fun ⟨_A,.cons p (.nil _)⟩ => rfl }
  source_eq _ := rfl
  dest_eq _ := rfl

def powerPoints : (n : Nat) → PointModel (P := P) (n+1) (positivePowers P S n)
  | 0 => primitivePoints S
  | n+1 => pointStep S (powerPoints n)

end ContextualComposition.GrothendieckStep.SpanApex
