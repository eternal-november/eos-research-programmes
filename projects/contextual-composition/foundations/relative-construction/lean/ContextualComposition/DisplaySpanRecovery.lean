module

public import Mathlib.CategoryTheory.Bicategory.Span.Basic
import all Mathlib.CategoryTheory.Bicategory.Span.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-! Display-span constructor of the relative-construction manuscript. The label fibre consists of the admitted objects of the slice, with every commuting apex map. -/

@[expose] public section

namespace ContextualComposition.DisplaySpanRecovery

open CategoryTheory CategoryTheory.Limits Opposite
universe v u
variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)
  {A B D A' B' D' : C}

abbrev Ext (A : C) := MorphismProperty.Over.forget P ⊤ A ⋙ CategoryTheory.Over.forget A
abbrev Native (A B : C) := CostructuredArrow (Ext P A) B
abbrev H (A B : C) := Span P ⊤ A B

def read : Native P A B ⥤ H P A B where
  obj x := ⟨x.left.left,x.left.hom,x.hom,x.left.prop,trivial⟩
  map f := ⟨f.left.left, MorphismProperty.Over.w f.left, CostructuredArrow.w f⟩

def write : H P A B ⥤ Native P A B where
  obj S := CostructuredArrow.mk (Y := MorphismProperty.Over.mk ⊤ S.l S.wl) S.r
  map f := CostructuredArrow.homMk (MorphismProperty.Over.homMk f.hom f.hom_l) f.hom_r

set_option backward.isDefEq.respectTransparency false in
def nativeEquivalence : Native P A B ≌ H P A B where
  functor := read P
  inverse := write P
  unitIso := NatIso.ofComponents (fun x =>
    CostructuredArrow.isoMk (MorphismProperty.Over.isoMk (Iso.refl _) (by simp [read,write])) (Category.id_comp x.hom))
    (by intro x y f; apply CostructuredArrow.hom_ext; apply MorphismProperty.Over.Hom.ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ => Span.mkIso (Iso.refl _) (by simp [read,write]) (by simp [read,write]))
    (by intro x y f; apply Span.hom_ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- An apex map over both endpoints. -/
structure Square (S : H P A B) (T : H P A' B') (u : A ⟶ A') (v : B ⟶ B') where
  apex : S.apex ⟶ T.apex
  source_comm : apex ≫ T.l = S.l ≫ u
  target_comm : apex ≫ T.r = S.r ≫ v

variable {P}

@[ext] theorem Square.ext {S : H P A B} {T : H P A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    {f g : Square P S T u v} (h : f.apex = g.apex) : f = g := by cases f; cases g; cases h; rfl

variable (P) [P.HasPullbacks]

local instance legPullback (T : H P A' B') (u : A ⟶ A') : HasPullback u T.l := by
  let := P.hasPullback u T.wl
  exact hasPullback_symmetry _ _

local instance nativePullback (x : Native P A B) (y : Native P B D) : HasPullback x.hom y.left.hom := by
  let := P.hasPullback x.hom y.left.prop
  exact hasPullback_symmetry _ _

/-- Native source-grade map into the reindexed display, with its body equation. -/
structure Reindexed (S : H P A B) (T : H P A' B') (u : A ⟶ A') (v : B ⟶ B') where
  grade : S.apex ⟶ pullback u T.l
  over : grade ≫ pullback.fst _ _ = S.l
  body : grade ≫ pullback.snd _ _ ≫ T.r = S.r ≫ v

theorem reindexed_admitted [P.IsStableUnderBaseChange] (T : H P A' B') (u : A ⟶ A') :
    P (pullback.fst u T.l) := P.pullback_fst _ _ T.wl

@[ext] theorem Reindexed.ext {S : H P A B} {T : H P A' B'} {u : A ⟶ A'} {v : B ⟶ B'}
    {f g : Reindexed P S T u v} (h : f.grade = g.grade) : f = g := by cases f; cases g; cases h; rfl

noncomputable def squareEquiv (S : H P A B) (T : H P A' B') (u : A ⟶ A') (v : B ⟶ B') :
    Reindexed P S T u v ≃ Square P S T u v where
  toFun f := {
    apex := f.grade ≫ pullback.snd _ _
    source_comm := by rw [Category.assoc, ← pullback.condition, ← Category.assoc, f.over]
    target_comm := by rw [Category.assoc, f.body] }
  invFun g := {
    grade := pullback.lift S.l g.apex g.source_comm.symm
    over := by simp
    body := by simp [g.target_comm] }
  left_inv f := by
    apply Reindexed.ext
    apply pullback.hom_ext <;> simp [f.over]
  right_inv g := Square.ext (by simp)

variable [P.IsMultiplicative] [P.IsStableUnderBaseChange]

/-- The chosen pullback composition with both legs and membership carried by the span type. -/
noncomputable abbrev comp (S : H P A B) (T : H P B D) : H P A D := Span.comp S T

/-- This is the bicategory with actual apex-map hom categories, canonical pullback associator, unitors, pentagon and triangle. -/
noncomputable abbrev coherent : Bicategory (Span.SpanBicat C P ⊤) := inferInstance

/-- Context reindexing along the first body and accumulation of its display. -/
noncomputable def nativeComp (x : Native P A B) (y : Native P B D) : Native P A D :=
  CostructuredArrow.mk (Y := MorphismProperty.Over.mk ⊤ (pullback.fst x.hom y.left.hom ≫ x.left.hom)
    (P.comp_mem _ _ (P.pullback_fst _ _ y.left.prop) x.left.prop)) (pullback.snd x.hom y.left.hom ≫ y.hom)

theorem read_nativeComp (x : Native P A B) (y : Native P B D) :
    (read P).obj (nativeComp P x y) = comp P ((read P).obj x) ((read P).obj y) := rfl

def nativeId (A : C) : Native P A A :=
  CostructuredArrow.mk (Y := MorphismProperty.Over.mk ⊤ (𝟙 A) (P.id_mem _)) (𝟙 A)

omit [P.HasPullbacks] [P.IsStableUnderBaseChange] in
theorem read_nativeId (A : C) : (read P).obj (nativeId P A) = Span.id A := rfl

noncomputable def paste {S : H P A B} {S' : H P A' B'} {T : H P B D} {T' : H P B' D'}
    {u : A ⟶ A'} {v : B ⟶ B'} {w : D ⟶ D'} (f : Square P S S' u v) (g : Square P T T' v w) :
    Square P (comp P S T) (comp P S' T') u w where
  apex := pullback.lift (pullback.fst S.r T.l ≫ f.apex) (pullback.snd S.r T.l ≫ g.apex) (by
    rw [Category.assoc, Category.assoc, f.target_comm, g.source_comm, ← Category.assoc, ← Category.assoc, pullback.condition])
  source_comm := by simp [Span.comp, f.source_comm, Category.assoc]
  target_comm := by simp [Span.comp, g.target_comm, Category.assoc]

open Bicategory

abbrev modelObject (A : C) : Span.SpanBicat C P ⊤ := ⟨A⟩
abbrev encoded (x : Native P A B) : modelObject P A ⟶ modelObject P B := (read P).obj x

/-- Every native hom-cell gives its actual apex square. -/
def fixed {x y : Native P A B} (f : x ⟶ y) : Square P (encoded P x) (encoded P y) (𝟙 A) (𝟙 B) :=
  ⟨f.left.left, (MorphismProperty.Over.w f.left).trans (Category.comp_id _).symm,
    (CostructuredArrow.w f).trans (Category.comp_id _).symm⟩

/-- The apex of native horizontal pasting is precisely the horizontal paste in the coherent span bicategory. -/
theorem paste_fixed {x x' : Native P A B} {y y' : Native P B D} (f : x ⟶ x') (g : y ⟶ y') :
    (paste P (fixed P f) (fixed P g)).apex =
      (((read P).map f ▷ encoded P y) ≫ (encoded P x' ◁ (read P).map g)).hom := by
  apply Span.SpanBicat.comp_hom_ext_apex (S₁ := encoded P x') (S₂ := encoded P y')
  · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _ ≫ _
    rw [pullback.lift_fst]
    let s := (read P).map f ▷ encoded P y
    let t := encoded P x' ◁ (read P).map g
    exact ((Category.assoc s.hom t.hom _).trans
      ((congrArg (s.hom ≫ ·) (Span.SpanBicat.whiskerLeft_hom_πₗ (encoded P x') ((read P).map g))).trans
        (Span.SpanBicat.whiskerRight_hom_πₗ ((read P).map f) (encoded P y)))).symm
  · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _ ≫ _
    rw [pullback.lift_snd]
    let s := (read P).map f ▷ encoded P y
    let t := encoded P x' ◁ (read P).map g
    exact ((Category.assoc s.hom t.hom _).trans
      ((congrArg (s.hom ≫ ·) (Span.SpanBicat.whiskerLeft_hom_πᵣ (encoded P x') ((read P).map g))).trans
        (Span.SpanBicat.whiskerRight_hom_πᵣ_assoc ((read P).map f) (encoded P y) ((read P).map g).hom))).symm

/-- The native associator is transported by the fixed-endpoint equivalence. The chosen compositions agree under reading by definition. -/
noncomputable def nativeAssociator {E : C} (x : Native P A B) (y : Native P B D) (z : Native P D E) :
    nativeComp P (nativeComp P x y) z ≅ nativeComp P x (nativeComp P y z) :=
  (nativeEquivalence P).fullyFaithfulFunctor.preimageIso (α_ (encoded P x) (encoded P y) (encoded P z))

theorem read_nativeAssociator {E : C} (x : Native P A B) (y : Native P B D) (z : Native P D E) :
    (read P).map (nativeAssociator P x y z).hom = (α_ (encoded P x) (encoded P y) (encoded P z)).hom :=
  (nativeEquivalence P).fullyFaithfulFunctor.map_preimage _

end ContextualComposition.DisplaySpanRecovery
