module

public import Mathlib.CategoryTheory.EqToHom

/-! An observation category for directed balance. An observation at a state supplies a left and right continuation; morphisms carry an actual state arrow and a map at each pair of compatible continuations. -/

@[expose] public section
namespace ContextualComposition.StateWindowCategory

open CategoryTheory
universe u v d w
variable {S : Type u} [Category.{v} S] (a b : S) (D : Type d) [Category.{w} D]

abbrev Window (s : S) := (a ⟶ s) × (s ⟶ b)

structure Object where
  state : S
  observe : Window a b state → D

variable {a b D}
structure Hom (x y : Object a b D) where
  state : x.state ⟶ y.state
  cell : ∀ (p : Window a b x.state) (q : Window a b y.state),
    p.1 ≫ state = q.1 → state ≫ q.2 = p.2 → (x.observe p ⟶ y.observe q)

@[ext] theorem Hom.ext {x y : Object a b D} {f g : Hom x y} (e : f.state=g.state)
    (c : ∀ p q h k h' k', f.cell p q h k = g.cell p q h' k') : f=g := by
  cases f with | mk a f =>
    cases g with | mk b g =>
      cases e
      have eq : f=g := by funext p q h k; exact c p q h k h k
      cases eq; rfl

def Hom.id (x : Object a b D) : Hom x x where
  state := 𝟙 _
  cell _ _ l r := eqToHom (congrArg x.observe
    (Prod.ext ((Category.comp_id _).symm.trans l) (r.symm.trans (Category.id_comp _))))

def Hom.comp {x y z : Object a b D} (f : Hom x y) (g : Hom y z) : Hom x z where
  state := f.state ≫ g.state
  cell p r l h := f.cell p (p.1 ≫ f.state,g.state ≫ r.2) rfl ((Category.assoc _ _ _).symm.trans h) ≫
    g.cell (p.1 ≫ f.state,g.state ≫ r.2) r ((Category.assoc _ _ _).trans l) rfl

theorem id_before {x y : Object a b D} (f : Hom x y) {p q : Window a b x.state} (r : Window a b y.state)
    (e : p=q) (l h l' h') :
    eqToHom (congrArg x.observe e) ≫ f.cell q r l h = f.cell p r l' h' := by subst q; exact Category.id_comp _
theorem id_after {x y : Object a b D} (f : Hom x y) (p : Window a b x.state) {q r : Window a b y.state}
    (e : q=r) (l h l' h') :
    f.cell p q l h ≫ eqToHom (congrArg y.observe e) = f.cell p r l' h' := by subst r; exact Category.comp_id _

theorem paste_three {x y z t : Object a b D} (f : Hom x y) (g : Hom y z) (k : Hom z t)
    (p : Window a b x.state) (q q' : Window a b y.state) (r r' : Window a b z.state) (s : Window a b t.state)
    (eq : q=q') (er : r=r') (l₁ h₁ l₂ h₂ l₃ h₃ l₁' h₁' l₂' h₂' l₃' h₃') :
    (f.cell p q l₁ h₁ ≫ g.cell q r l₂ h₂) ≫ k.cell r s l₃ h₃ =
    f.cell p q' l₁' h₁' ≫ g.cell q' r' l₂' h₂' ≫ k.cell r' s l₃' h₃' := by
  subst q'; subst r'; exact Category.assoc _ _ _

instance : Category (Object a b D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (Category.id_comp _) (fun p q l h l' h' =>
    id_before f q (Prod.ext (Category.comp_id _).symm h'.symm) _ _ _ _)
  comp_id f := Hom.ext (Category.comp_id _) (fun p q l h l' h' =>
    id_after f p (Prod.ext l' (Category.id_comp _)) _ _ _ _)
  assoc f g k := by
    apply Hom.ext (Category.assoc _ _ _)
    intro p s l h l' h'
    apply paste_three f g k p
      (p.1 ≫ f.state,g.state ≫ k.state ≫ s.2) (p.1 ≫ f.state,(g.state ≫ k.state) ≫ s.2)
      (p.1 ≫ (f.state ≫ g.state), k.state ≫ s.2) ((p.1 ≫ f.state) ≫ g.state,k.state ≫ s.2)
      s (Prod.ext rfl (Category.assoc _ _ _).symm) (Prod.ext (Category.assoc _ _ _).symm rfl)

end ContextualComposition.StateWindowCategory
