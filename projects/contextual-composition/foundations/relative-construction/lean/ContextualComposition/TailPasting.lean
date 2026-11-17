module
public import ContextualComposition.SquarePasting
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares
open CategoryTheory Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (Y : Bᵒᵖ ⥤ Cat.{v,u}) (S : P.Split)

def rebaseDecorated {n A D} {a b : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))} (h : a = b)
    (f : DecoratedHom Y a t z x y) : DecoratedHom Y b t z x y := h ▸ f

theorem rebaseDecorated_data {n A D} {a b : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))} (h : a = b)
    (f : DecoratedHom Y a t z x y) : rebaseDecorated Y h f =
      ⟨rebaseSquare h f.1, f.2 ≫ eqToHom (congrArg (fun k => (Y.map k.op).toFunctor.obj y)
        (terminal_rebase h f.1).symm)⟩ := by
  subst b
  exact congrArg (Sigma.mk f.1) (Category.comp_id f.2).symm

theorem comparison_rebase {n A D} {a b : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))} (h : a = b)
    (f : DecoratedHom Y a t z x y) :
    squareEquiv Y S b t z x y (rebaseDecorated Y h f) =
      squareEquiv Y S a t z x y f ≫ eqToHom (congrArg
        (fun k => ((Iterates.layer P S Y n).map k.op).toFunctor.obj (realize Y S z y)) h) := by
  subst b; simp [rebaseDecorated]

private theorem cast_target {C : Type*} [Category* C] {x a b : C}
    (h : a = b) (f : x ⟶ a) : Equiv.cast (congrArg (fun dest => (x ⟶ dest)) h) f =
      f ≫ eqToHom h := by subst b; simp

theorem compared_tail {n A D} {a : A ⟶ D} {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    {t : Chain P n ((P.extend A).obj p)} {z : Chain P n ((P.extend D).obj q)}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    (f : DecoratedHom Y a (.cons p t) (.cons q z) x y) :
    payloadMap (squareEquiv Y S a (.cons p t) (.cons q z) x y f) =
      squareEquiv Y S (next a f.1.1) t z x y ⟨f.1.2,f.2⟩ ≫
        eqToHom (tailTarget Y S a f.1.1 (realize Y S z y)) := by
  apply cast_target

section
variable {n : Nat} {A D E : B} {a : A ⟶ D} {b : D ⟶ E}
    {p : P.grades.obj (op A)} {q : P.grades.obj (op D)} {r : P.grades.obj (op E)}
    {t : Chain P n ((P.extend A).obj p)} {z : Chain P n ((P.extend D).obj q)}
    {w : Chain P n ((P.extend E).obj r)} {x : Y.obj (op (endpoint t))}
    {y : Y.obj (op (endpoint z))} {h : Y.obj (op (endpoint w))}
    (f : DecoratedHom Y a (.cons p t) (.cons q z) x y)
    (g : DecoratedHom Y b (.cons q z) (.cons r w) y h)

def tailPart {A D : B} {a : A ⟶ D} {p : P.grades.obj (op A)} {q : P.grades.obj (op D)}
    {t : Chain P n ((P.extend A).obj p)} {z : Chain P n ((P.extend D).obj q)}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))}
    (f : DecoratedHom Y a (.cons p t) (.cons q z) x y) :
    DecoratedHom Y (next a f.1.1) t z x y := ⟨f.1.2,f.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem tail_paste :
    tailPart Y (decoratedComp S Y f g) = rebaseDecorated Y (next_comp S f.1.1 g.1.1).symm
      (decoratedComp S Y (tailPart Y f) (tailPart Y g)) := by
  rw [rebaseDecorated_data]
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  change (_ ≫ _ ≫ eqToHom _) = (_ ≫ _ ≫ eqToHom _) ≫ eqToHom _
  simp (config := {zeta := true}) only [Category.assoc,eqToHom_trans]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem compared_paste_tail :
    payloadMap (squareEquiv Y S (a ≫ b) (.cons p t) (.cons r w) x h (decoratedComp S Y f g)) =
      squareEquiv Y S (next a f.1.1 ≫ next b g.1.1) t w x h
        (decoratedComp S Y (tailPart Y f) (tailPart Y g)) ≫
      eqToHom ((congrArg (fun k => ((Iterates.layer P S Y n).map k.op).toFunctor.obj (realize Y S w h))
        (next_comp S f.1.1 g.1.1).symm).trans
          (tailTarget Y S (a ≫ b) (headComp (P := P) f.1.1 g.1.1) (realize Y S w h))) := by
  rw [compared_tail]
  change squareEquiv Y S _ _ _ _ _ (tailPart Y (decoratedComp S Y f g)) ≫ _ = _
  rw [tail_paste,comparison_rebase,Category.assoc,eqToHom_trans]

end

/-- Native dependent composition in a strict category-valued presheaf, including
the correction from sequential to composite pullback. -/
def nativePaste {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Cat.{v,u})
    {A D E : C} {a : A ⟶ D} {b : D ⟶ E} {x : F.obj (op A)} {y : F.obj (op D)} {z : F.obj (op E)}
    (f : x ⟶ (F.map a.op).toFunctor.obj y) (g : y ⟶ (F.map b.op).toFunctor.obj z) :
    x ⟶ (F.map (a ≫ b).op).toFunctor.obj z :=
  f ≫ (F.map a.op).toFunctor.map g ≫ eqToHom (by rw [op_comp,F.map_comp]; rfl)

set_option backward.isDefEq.respectTransparency false in
theorem one_tail_native {A D E : B} {a : A ⟶ D} {b : D ⟶ E}
    {p : P.grades.obj (op A)} {q : P.grades.obj (op D)} {r : P.grades.obj (op E)}
    {x : Y.obj (op ((P.extend A).obj p))} {y : Y.obj (op ((P.extend D).obj q))}
    {h : Y.obj (op ((P.extend E).obj r))}
    (f : DecoratedHom Y a (.cons p (.nil _)) (.cons q (.nil _)) x y)
    (g : DecoratedHom Y b (.cons q (.nil _)) (.cons r (.nil _)) y h) :
    payloadMap (squareEquiv Y S (a ≫ b) (.cons p (.nil _)) (.cons r (.nil _)) x h
      (decoratedComp S Y f g)) =
    nativePaste Y (a := next a f.1.1) (b := next b g.1.1) (x := x) (y := y) (z := h) f.2 g.2 ≫
      eqToHom ((congrArg (fun k : (P.extend A).obj p ⟶ (P.extend E).obj r => (Y.map k.op).toFunctor.obj h) (next_comp S f.1.1 g.1.1).symm).trans
        (tailTarget Y S (n := 0) (a ≫ b) (headComp (P := P) f.1.1 g.1.1) h)) := by
  apply compared_paste_tail

namespace FamilyComparison
open Families
abbrev single {A : Type} (p : presheaf.obj (op A)) : Chain endpoints 1 A :=
  .cons p (.nil _)

set_option backward.isDefEq.respectTransparency false in
theorem one_comp {A D E : Type} {a : A ⟶ D} {b : D ⟶ E}
    {p : presheaf.obj (op A)} {q : presheaf.obj (op D)} {r : presheaf.obj (op E)}
    {x : presheaf.obj (op (endpoint (single p)))} {y : presheaf.obj (op (endpoint (single q)))}
    {h : presheaf.obj (op (endpoint (single r)))}
    (f : DecoratedHom presheaf a (single p) (single q) x y)
    (g : DecoratedHom presheaf b (single q) (single r) y h) :
    squareEquiv presheaf splitEndpoints (a ≫ b) (single p) (single r) x h
      (decoratedComp splitEndpoints presheaf f g) =
      nativePaste (Iterates.layer endpoints splitEndpoints presheaf 1) (a := a) (b := b)
        (x := realize presheaf splitEndpoints (single p) x)
        (y := realize presheaf splitEndpoints (single q) y)
        (z := realize presheaf splitEndpoints (single r) h)
        (squareEquiv presheaf splitEndpoints a (single p) (single q) x y f)
        (squareEquiv presheaf splitEndpoints b (single q) (single r) y h g) := by
  apply (homEquiv _ _).injective
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  apply ConcreteCategory.hom_ext
  intro t
  rfl
end FamilyComparison
end ContextualComposition.GrothendieckStep.TelescopeSquares
