module
public import ContextualComposition.TelescopeSquares
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares
open CategoryTheory Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B}

private theorem lift_transport {K L : Type*} [Category* K] [Category* L] {r s : K ⥤ L}
    {d : L ⥤ B} {e : K ⥤ B} {l : r ⋙ d ⟶ e} {m : s ⋙ d ⟶ e}
    (h : s = r) (j : HEq m l) (p : K) :
    d.map (eqToHom (Functor.congr_obj h p).symm) ≫ m.app p = l.app p := by
  subst s
  cases eq_of_heq j
  simp

def headId {A : B} (p : P.grades.obj (op A)) :
    p ⟶ (P.grades.map (𝟙 A).op).toFunctor.obj p :=
  eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (P.grades.map_id (op A))) p).symm

def headComp {A D E : B} {a : A ⟶ D} {b : D ⟶ E}
    {p : P.grades.obj (op A)} {q : P.grades.obj (op D)} {r : P.grades.obj (op E)}
    (k : p ⟶ (P.grades.map a.op).toFunctor.obj q) (j : q ⟶ (P.grades.map b.op).toFunctor.obj r) :
    p ⟶ (P.grades.map (a ≫ b).op).toFunctor.obj r :=
  k ≫ (P.grades.map a.op).toFunctor.map j ≫
    eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (P.grades.map_comp b.op a.op)) r).symm

variable (S : P.Split)
include S
theorem next_id {A : B} (p : P.grades.obj (op A)) :
    next (𝟙 A) (headId (P := P) p) = 𝟙 _ :=
  lift_transport (r := 𝟭 _) (m := P.lift (𝟙 A)) (l := 𝟙 (P.extend A))
    (congrArg Cat.Hom.toFunctor (P.grades.map_id (op A))) (S.lift_id A) p

theorem next_comp {A D E : B} {a : A ⟶ D} {b : D ⟶ E}
    {p : P.grades.obj (op A)} {q : P.grades.obj (op D)} {r : P.grades.obj (op E)}
    (k : p ⟶ (P.grades.map a.op).toFunctor.obj q) (j : q ⟶ (P.grades.map b.op).toFunctor.obj r) :
    next (a ≫ b) (headComp (P := P) k j) = next a k ≫ next b j := by
  have h := lift_transport (m := P.lift (a ≫ b))
    (l := pasteLift _ _ _ _ _ (P.lift b) (P.lift a))
    (congrArg Cat.Hom.toFunctor (P.grades.map_comp b.op a.op)) (S.lift_comp b a) r
  unfold next headComp
  simp only [Functor.map_comp,Category.assoc]
  rw [h]
  change _ ≫ _ ≫ (P.lift a).app _ ≫ _ = _
  rw [← Category.assoc ((P.extend A).map ((P.grades.map a.op).toFunctor.map j))]
  rw [show (P.extend A).map ((P.grades.map a.op).toFunctor.map j) ≫ (P.lift a).app _ =
    (P.lift a).app _ ≫ (P.extend D).map j from (P.lift a).naturality j]
  simp only [Category.assoc]

omit S in
def rebaseSquare {n A D} {t : Chain P n A} {z : Chain P n D} {a b : A ⟶ D}
    (h : a = b) (s : Square a t z) : Square b t z := h ▸ s

omit S in
theorem terminal_rebase {n A D} {t : Chain P n A} {z : Chain P n D} {a b : A ⟶ D}
    (h : a = b) (s : Square a t z) :
    terminalMap (t := t) (z := z) (u := b) (rebaseSquare h s) = terminalMap s := by
  subst b; rfl

def squareId : {n : Nat} → {A : B} → (t : Chain P n A) → Square (𝟙 A) t t
  | 0, _, .nil _ => PUnit.unit
  | _+1, _, .cons p t =>
    ⟨headId p,rebaseSquare (t := t) (z := t) (next_id S p).symm (squareId t)⟩

def squareComp : {n : Nat} → {A D E : B} → {a : A ⟶ D} → {b : D ⟶ E} →
    {t : Chain P n A} → {z : Chain P n D} → {w : Chain P n E} →
    Square a t z → Square b z w → Square (a ≫ b) t w
  | 0, _, _, _, _, _, .nil _, .nil _, .nil _, _, _ => PUnit.unit
  | n+1, _, _, _, a, b, .cons _ t, .cons _ z, .cons _ w, f, g =>
    ⟨headComp f.1 g.1,rebaseSquare (t := t) (z := w) (next_comp S f.1 g.1).symm
      (@squareComp n _ _ _ (next a f.1) (next b g.1) t z w f.2 g.2)⟩

theorem terminal_id : {n : Nat} → {A : B} → (t : Chain P n A) →
    terminalMap (u := 𝟙 A) (t := t) (z := t) (squareId S t) = 𝟙 _
  | 0, _, .nil _ => rfl
  | _+1, _, .cons _ t => (terminal_rebase _ _).trans (terminal_id t)

theorem terminal_comp : {n : Nat} → {A D E : B} → {a : A ⟶ D} → {b : D ⟶ E} →
    {t : Chain P n A} → {z : Chain P n D} → {w : Chain P n E} →
    (f : Square a t z) → (g : Square b z w) →
    terminalMap (u := a ≫ b) (t := t) (z := w) (squareComp S f g) = terminalMap f ≫ terminalMap g
  | 0, _, _, _, _, _, .nil _, .nil _, .nil _, _, _ => rfl
  | n+1, _, _, _, a, b, .cons _ t, .cons _ z, .cons _ w, f, g =>
    (terminal_rebase _ _).trans (@terminal_comp n _ _ _ (next a f.1) (next b g.1) t z w f.2 g.2)
variable (Y : Bᵒᵖ ⥤ Cat.{v,u})
def decoratedId {n A} (t : Chain P n A) (x : Y.obj (op (endpoint t))) :
    DecoratedHom Y (𝟙 A) t t x x :=
  ⟨squareId S t, eqToHom (by rw [terminal_id,op_id,Y.map_id]; rfl)⟩

theorem payloadTarget {n A D E} {a : A ⟶ D} {b : D ⟶ E} {t : Chain P n A} {z : Chain P n D}
    {w : Chain P n E} (f : Square a t z) (g : Square b z w) (x : Y.obj (op (endpoint w))) :
    (Y.map (terminalMap f).op).toFunctor.obj ((Y.map (terminalMap g).op).toFunctor.obj x) =
      (Y.map (terminalMap (u := a ≫ b) (t := t) (z := w) (squareComp S f g)).op).toFunctor.obj x := by
  rw [terminal_comp,op_comp,Y.map_comp]; rfl

def decoratedComp {n A D E} {a : A ⟶ D} {b : D ⟶ E} {t : Chain P n A} {z : Chain P n D}
    {w : Chain P n E} {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    {h : Y.obj (op (endpoint w))} (f : DecoratedHom Y a t z x y) (g : DecoratedHom Y b z w y h) :
    DecoratedHom Y (a ≫ b) t w x h :=
  ⟨squareComp S f.1 g.1, f.2 ≫ (Y.map (terminalMap f.1).op).toFunctor.map g.2 ≫
    eqToHom (payloadTarget S Y f.1 g.1 h)⟩

/-- The independent pasted head is retained by the actual comparison even when
the nontrivial tail must be transported along the endpoint equality. -/
theorem compared_head {n A D} {a : A ⟶ D} {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    {t : Chain P n ((P.extend A).obj p)} {z : Chain P n ((P.extend D).obj q)}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    (f : DecoratedHom Y a (.cons p t) (.cons q z) x y) :
    gradeMap ((squareEquiv Y S a (.cons p t) (.cons q z) x y) f) = f.1.1 := rfl

theorem compared_comp_head {n A D E} {a : A ⟶ D} {b : D ⟶ E}
    {p : P.grades.obj (op A)} {q : P.grades.obj (op D)} {r : P.grades.obj (op E)}
    {t : Chain P n ((P.extend A).obj p)} {z : Chain P n ((P.extend D).obj q)}
    {w : Chain P n ((P.extend E).obj r)} {x : Y.obj (op (endpoint t))}
    {y : Y.obj (op (endpoint z))} {h : Y.obj (op (endpoint w))}
    (f : DecoratedHom Y a (.cons p t) (.cons q z) x y)
    (g : DecoratedHom Y b (.cons q z) (.cons r w) y h) :
    gradeMap ((squareEquiv Y S (a ≫ b) (.cons p t) (.cons r w) x h)
      (decoratedComp S Y f g)) = headComp (P := P) f.1.1 g.1.1 := rfl

theorem compared_zero_comp {A D E : B} {a : A ⟶ D} {b : D ⟶ E}
    {x : Y.obj (op A)} {y : Y.obj (op D)} {h : Y.obj (op E)}
    (f : DecoratedHom Y a (Chain.nil (P := P) A) (.nil D) x y)
    (g : DecoratedHom Y b (Chain.nil (P := P) D) (.nil E) y h) :
    squareEquiv Y S (a ≫ b) (.nil A) (.nil E) x h (decoratedComp S Y f g) =
      (squareEquiv Y S a (.nil A) (.nil D) x y f) ≫
        (Y.map a.op).toFunctor.map (squareEquiv Y S b (.nil D) (.nil E) y h g) ≫
        eqToHom (payloadTarget S Y f.1 g.1 h) := rfl

omit S
namespace Example
open Families
def preSrc : Chain endpoints 2 Bool := .cons (fun _ => Unit) (.cons (fun _ => Unit) (.nil _))
def preSquare : Square collapse preSrc src :=
  ⟨fun _ => TypeCat.ofHom id,fun _ => TypeCat.ofHom id,PUnit.unit⟩
theorem pasted_test (b i : Bool) :
    terminalMap (u := collapse ≫ selectPoint b) (t := preSrc) (z := dst)
      (squareComp splitEndpoints preSquare (sq b)) ⟨⟨i,()⟩,()⟩ = ⟨⟨b,true⟩,false⟩ := by
  rw [terminal_comp]; rfl
end Example
end ContextualComposition.GrothendieckStep.TelescopeSquares
