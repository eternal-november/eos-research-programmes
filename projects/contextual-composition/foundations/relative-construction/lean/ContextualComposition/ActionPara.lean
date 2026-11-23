module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! Forward Para on an arbitrary right monoidal action, from the relative
construction manuscript's section on internal constructors. We use the actual
costructured-arrow category of the extension at the source. -/

@[expose] public section

namespace ContextualComposition.ActionPara

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.MonoidalRightAction

universe u v w z

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
variable {C : Type w} [Category.{z} C] [MonoidalRightAction V C]

/-- The source-indexed extension functor of the constant parameter fibre. -/
abbrev extension (V : Type u) [Category.{v} V] [MonoidalCategory V] [MonoidalRightAction V C]
    (A : C) : V ⥤ C where
  obj P := A ⊙ᵣ P
  map p := A ⊴ᵣ p

abbrev Arrow (V : Type u) [Category.{v} V] [MonoidalCategory V] [MonoidalRightAction V C] (A B : C) :=
  CostructuredArrow (extension V A) B

variable {A B D E F A' B' D' E' A'' B'' D'' : C}

structure Square (f : Arrow V A B) (g : Arrow V A' B') (u : A ⟶ A') (v : B ⟶ B') where
  param : f.left ⟶ g.left
  comm : (u ⊙ᵣₘ param) ≫ g.hom = f.hom ≫ v

@[ext] theorem square_ext {f : Arrow V A B} {g : Arrow V A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    {s t : Square f g u v} (h : s.param = t.param) : s = t := by
  cases s; cases t; cases h; rfl

/-- At fixed endpoints the native squares are exactly the comma morphisms. -/
def globular (f g : Arrow V A B) : (f ⟶ g) ≃ Square f g (𝟙 A) (𝟙 B) where
  toFun h := ⟨h.left, by simpa using CostructuredArrow.w h⟩
  invFun s := CostructuredArrow.homMk s.param (by simpa using s.comm)
  left_inv _ := CostructuredArrow.hom_ext _ _ rfl
  right_inv _ := square_ext rfl

def targetChange (f : Arrow V A B) (v : B ⟶ B') : Arrow V A B' :=
  CostructuredArrow.mk (f.hom ≫ v)

def sourceChange (u : A ⟶ A') (g : Arrow V A' B') : Arrow V A B' :=
  CostructuredArrow.mk ((u ⊵ᵣ g.left) ≫ g.hom)

/-- Arbitrary endpoint squares are the native comma cells after transporting
both bodies to the common hom-category. Both maps retain the given parameter. -/
def endpointCells (f : Arrow V A B) (g : Arrow V A' B') (u : A ⟶ A') (v : B ⟶ B') :
    (targetChange f v ⟶ sourceChange u g) ≃ Square f g u v where
  toFun h := ⟨h.left, by
    change (u ⊙ᵣₘ h.left) ≫ g.hom = f.hom ≫ v
    erw [actionHom_def', Category.assoc]
    exact CostructuredArrow.w h⟩
  invFun s := CostructuredArrow.homMk s.param (by
    change (A ⊴ᵣ s.param) ≫ (u ⊵ᵣ g.left) ≫ g.hom = f.hom ≫ v
    simpa only [actionHom_def', Category.assoc] using s.comm)
  left_inv _ := CostructuredArrow.hom_ext _ _ rfl
  right_inv _ := square_ext rfl

def squareId (f : Arrow V A B) : Square f f (𝟙 A) (𝟙 B) := ⟨𝟙 _, by simp⟩

def vertical {f : Arrow V A B} {g : Arrow V A' B'} {h : Arrow V A'' B''}
    {u : A ⟶ A'} {v : B ⟶ B'} {u' : A' ⟶ A''} {v' : B' ⟶ B''}
    (s : Square f g u v) (t : Square g h u' v') : Square f h (u ≫ u') (v ≫ v') where
  param := s.param ≫ t.param
  comm := by simp only [actionHom_comp, Category.assoc, t.comm, reassoc_of% s.comm]

def pure (u : A ⟶ B) : Arrow V A B :=
  CostructuredArrow.mk ((ρᵣ[V] A).hom ≫ u)

def pureSquare {f : A ⟶ B} {g : A' ⟶ B'} {u : A ⟶ A'} {v : B ⟶ B'} (h : u ≫ g = f ≫ v) :
    Square (pure (V := V) f) (pure g) u v where
  param := 𝟙 _
  comm := by simp [pure, Category.assoc, h]

def comp (f : Arrow V A B) (g : Arrow V B D) : Arrow V A D :=
  CostructuredArrow.mk ((αᵣ A f.left g.left).hom ≫ (f.hom ⊵ᵣ g.left) ≫ g.hom)

private theorem paste_step {X X' Y Y' : C} {T T' M M' : V} {u : X ⟶ X'} {v : Y ⟶ Y'}
    {k : T ⟶ T'} {f : X ⊙ᵣ T ⟶ Y} {f' : X' ⊙ᵣ T' ⟶ Y'}
    (h : (u ⊙ᵣₘ k) ≫ f' = f ≫ v) (l : M ⟶ M') :
    ((u ⊙ᵣₘ k) ⊙ᵣₘ l) ≫ (f' ⊵ᵣ M') = (f ⊵ᵣ M) ≫ (v ⊙ᵣₘ l) := by
  rw [← actionHom_id, ← actionHom_id f, ← actionHom_comp, ← actionHom_comp]
  simp [h]

def horizontal {f : Arrow V A B} {g : Arrow V B D} {f' : Arrow V A' B'} {g' : Arrow V B' D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'} (s : Square f f' u v) (t : Square g g' v w) :
    Square (comp f g) (comp f' g') u w where
  param := s.param ⊗ₘ t.param
  comm := by
    change (u ⊙ᵣₘ s.param ⊗ₘ t.param) ≫ (αᵣ _ _ _).hom ≫ _ ≫ _ = (_ ≫ _ ≫ _) ≫ w
    rw [actionAssocIso_hom_naturality_assoc, reassoc_of% (paste_step s.comm t.param), t.comm]
    simp only [Category.assoc]

theorem horizontal_identity (f : Arrow V A B) (g : Arrow V B D) :
    horizontal (squareId f) (squareId g) = squareId (comp f g) := by
  apply square_ext
  change (𝟙 f.left) ⊗ₘ (𝟙 g.left) = _
  simp [squareId, comp]

theorem interchange {f : Arrow V A B} {g : Arrow V B D} {f' : Arrow V A' B'} {g' : Arrow V B' D'}
    {f'' : Arrow V A'' B''} {g'' : Arrow V B'' D''}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'} {u' : A' ⟶ A''} {v' : B' ⟶ B''} {w' : D' ⟶ D''}
    (s : Square f f' u v) (t : Square g g' v w) (s' : Square f' f'' u' v') (t' : Square g' g'' v' w') :
    horizontal (vertical s s') (vertical t t') = vertical (horizontal s t) (horizontal s' t') := by
  apply square_ext
  exact (tensorHom_comp_tensorHom _ _ _ _).symm

def horizontalHom {f f' : Arrow V A B} {g g' : Arrow V B D} (s : f ⟶ f') (t : g ⟶ g') :
    comp f g ⟶ comp f' g' :=
  (globular _ _).symm (horizontal (globular _ _ s) (globular _ _ t))

@[simp] theorem horizontalHom_left {f f' : Arrow V A B} {g g' : Arrow V B D} (s : f ⟶ f') (t : g ⟶ g') :
    (horizontalHom s t).left = s.left ⊗ₘ t.left := rfl

def associator (f : Arrow V A B) (g : Arrow V B D) (h : Arrow V D E) :
    comp (comp f g) h ≅ comp f (comp g h) := by
  refine CostructuredArrow.isoMk (α_ f.left g.left h.left) ?_
  simp [comp, extension, Category.assoc]

def leftUnitor (f : Arrow V A B) : comp (pure (𝟙 A)) f ≅ f := by
  refine CostructuredArrow.isoMk (λ_ f.left) ?_
  simp [comp, pure, extension, Category.assoc]

def rightUnitor (f : Arrow V A B) : comp f (pure (𝟙 B)) ≅ f := by
  refine CostructuredArrow.isoMk (ρ_ f.left) ?_
  simp [comp, pure, extension, Category.assoc]

theorem associator_naturality {f f' : Arrow V A B} {g g' : Arrow V B D} {h h' : Arrow V D E}
    (s : f ⟶ f') (t : g ⟶ g') (r : h ⟶ h') :
    horizontalHom (horizontalHom s t) r ≫ (associator f' g' h').hom =
      (associator f g h).hom ≫ horizontalHom s (horizontalHom t r) := by
  apply CostructuredArrow.hom_ext
  exact MonoidalCategory.associator_naturality s.left t.left r.left

theorem leftUnitor_naturality {f f' : Arrow V A B} (s : f ⟶ f') :
    horizontalHom (𝟙 (pure (V := V) (𝟙 A))) s ≫ (leftUnitor f').hom = (leftUnitor f).hom ≫ s := by
  apply CostructuredArrow.hom_ext
  change (𝟙 _ ⊗ₘ s.left) ≫ (λ_ _).hom = _
  rw [id_tensorHom]
  exact MonoidalCategory.leftUnitor_naturality s.left

theorem rightUnitor_naturality {f f' : Arrow V A B} (s : f ⟶ f') :
    horizontalHom s (𝟙 (pure (V := V) (𝟙 B))) ≫ (rightUnitor f').hom = (rightUnitor f).hom ≫ s := by
  apply CostructuredArrow.hom_ext
  change (s.left ⊗ₘ 𝟙 _) ≫ (ρ_ _).hom = _
  rw [tensorHom_id]
  exact MonoidalCategory.rightUnitor_naturality s.left

theorem pentagon (f : Arrow V A B) (g : Arrow V B D) (h : Arrow V D E) (k : Arrow V E F) :
    horizontalHom (associator f g h).hom (𝟙 k) ≫ (associator f (comp g h) k).hom ≫
      horizontalHom (𝟙 f) (associator g h k).hom =
      (associator (comp f g) h k).hom ≫ (associator f g (comp h k)).hom := by
  apply CostructuredArrow.hom_ext
  change ((α_ _ _ _).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ (α_ _ _ _).hom) = _
  rw [tensorHom_id, id_tensorHom]
  exact MonoidalCategory.pentagon f.left g.left h.left k.left

theorem triangle (f : Arrow V A B) (g : Arrow V B D) :
    (associator f (pure (𝟙 B)) g).hom ≫ horizontalHom (𝟙 f) (leftUnitor g).hom =
      horizontalHom (rightUnitor f).hom (𝟙 g) := by
  apply CostructuredArrow.hom_ext
  change (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ (λ_ _).hom) = ((ρ_ _).hom ⊗ₘ 𝟙 _)
  rw [tensorHom_id, id_tensorHom]
  exact MonoidalCategory.triangle f.left g.left

def pureCompIso (u : A ⟶ B) (v : B ⟶ D) : comp (pure (V := V) u) (pure v) ≅ pure (u ≫ v) := by
  refine CostructuredArrow.isoMk (λ_ (𝟙_ V)) ?_
  simp [comp, pure, extension, Category.assoc]

def rebind {f : Arrow V A B} {g : Arrow V A' B'} {u u' : A ⟶ A'} {v v' : B ⟶ B'}
    (s : Square f g u v) (hu : u = u') (hv : v = v') : Square f g u' v' :=
  ⟨s.param, hu ▸ hv ▸ s.comm⟩

def postCell {f : Arrow V A B} {g g' : Arrow V A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    (s : Square f g u v) (h : g ⟶ g') : Square f g' u v :=
  rebind (vertical s (globular _ _ h)) (Category.comp_id _) (Category.comp_id _)

def preCell {f f' : Arrow V A B} {g : Arrow V A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    (h : f ⟶ f') (s : Square f' g u v) : Square f g u v :=
  rebind (vertical (globular _ _ h) s) (Category.id_comp _) (Category.id_comp _)

theorem associator_endpoint_naturality {f : Arrow V A B} {g : Arrow V B D} {h : Arrow V D E}
    {f' : Arrow V A' B'} {g' : Arrow V B' D'} {h' : Arrow V D' E'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'} {x : E ⟶ E'}
    (s : Square f f' u v) (t : Square g g' v w) (r : Square h h' w x) :
    postCell (horizontal (horizontal s t) r) (associator f' g' h').hom =
      preCell (associator f g h).hom (horizontal s (horizontal t r)) := by
  apply square_ext
  exact MonoidalCategory.associator_naturality s.param t.param r.param

theorem leftUnitor_endpoint_naturality {f : Arrow V A B} {g : Arrow V A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    (s : Square f g u v) :
    postCell (horizontal (pureSquare (show u ≫ 𝟙 A' = 𝟙 A ≫ u by simp)) s) (leftUnitor g).hom =
      preCell (leftUnitor f).hom s := by
  apply square_ext
  change (𝟙 _ ⊗ₘ s.param) ≫ (λ_ _).hom = _
  rw [id_tensorHom]
  exact MonoidalCategory.leftUnitor_naturality s.param

theorem rightUnitor_endpoint_naturality {f : Arrow V A B} {g : Arrow V A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    (s : Square f g u v) :
    postCell (horizontal s (pureSquare (show v ≫ 𝟙 B' = 𝟙 B ≫ v by simp))) (rightUnitor g).hom =
      preCell (rightUnitor f).hom s := by
  apply square_ext
  change (s.param ⊗ₘ 𝟙 _) ≫ (ρ_ _).hom = _
  rw [tensorHom_id]
  exact MonoidalCategory.rightUnitor_naturality s.param

end ContextualComposition.ActionPara
