module
public import ContextualComposition.NativeCommaProducts
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! With display all maps and constant content at B, the native hom is the category of spans over A and B. Its slice representation keeps every apex map. -/

@[expose] public section
noncomputable section
namespace ContextualComposition.NativeSpanProducts
open CategoryTheory CategoryTheory.Limits NativeCommaProducts
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {C : Type u} [Category.{v} C]
abbrev One := Discrete PUnit.{1}
abbrev content (B : C) : One ⥤ C := (Functor.const _).obj B
abbrev Spans (A B : C) := Comma (Over.forget A) (content B)
variable {A B : C}

/-- Every slice arrow is cartesian for the domain extension functor, including noninvertible arrows. -/
theorem domain_cartesian {P Q : Over A} (c : P ⟶ Q) :
    (Over.forget A).IsStronglyCartesian ((Over.forget A).map c) c where
  universal_property' {R} k f _ := by
    have base : k ≫ c.left = f.left := IsHomLift.eq_of_isHomLift (Over.forget A) (k ≫ (Over.forget A).map c) f
    have triangle : k ≫ P.hom = R.hom := by rw [← Over.w c,← Category.assoc,base,Over.w f]
    let h : R ⟶ P := Over.homMk k triangle
    refine ⟨h,⟨(inferInstance : (Over.forget A).IsHomLift ((Over.forget A).map h) h),?_⟩,?_⟩
    · apply Over.OverMorphism.ext; exact base
    · rintro g ⟨over,_⟩
      let := over
      apply Over.OverMorphism.ext
      exact (IsHomLift.eq_of_isHomLift (Over.forget A) k g).symm

/-- For a slice projection, the cartesian lift of an arbitrary map is ordinary precomposition of the apex structure arrow. -/
def domainLift {P : Over A} {X : C} (k : X ⟶ P.left) : Over.mk (k ≫ P.hom) ⟶ P :=
  Over.homMk k rfl

variable (A B) [HasBinaryProduct A B]

def pack : Spans A B ⥤ Over (A ⨯ B) where
  obj X := Over.mk (prod.lift X.left.hom X.hom)
  map f := Over.homMk f.left.left (by
    apply prod.hom_ext
    · simp
    · simpa [content] using f.w)

def unpack : Over (A ⨯ B) ⥤ Spans A B where
  obj X := ⟨Over.mk (X.hom ≫ prod.fst),⟨⟨⟩⟩,X.hom ≫ prod.snd⟩
  map f := {
    left := Over.homMk f.left (by simp)
    right := 𝟙 _
    w := by simp [content] }

def equivalence : Spans A B ≌ Over (A ⨯ B) where
  functor := pack A B
  inverse := unpack A B
  unitIso := NatIso.ofComponents (fun X =>
    Comma.isoMk (Over.isoMk (Iso.refl _) (by simp [pack,unpack])) (eqToIso (Subsingleton.elim _ _))
      (by simp [pack,unpack,content])) (by intro X Y f; ext <;> simp [pack,unpack])
  counitIso := NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _) (by
    apply prod.hom_ext <;> simp [pack,unpack])) (by intro X Y f; ext; simp [pack,unpack])

/-- The terminal span has apex A × B. -/
def terminalSpan : Spans A B := ⟨Over.mk (prod.fst (X:=A) (Y:=B)),⟨⟨⟩⟩,prod.snd (X:=A) (Y:=B)⟩

def terminalIsTerminal : IsTerminal (terminalSpan A B) :=
  IsTerminal.ofUniqueHom (fun X =>
    ⟨Over.homMk (prod.lift (X:=A) (Y:=B) X.left.hom X.hom) (by simp [terminalSpan]),eqToHom (Subsingleton.elim _ _),
      by simp [terminalSpan,content]⟩)
    (by
      intro X f
      apply Comma.hom_ext
      · apply Over.OverMorphism.ext
        apply prod.hom_ext
        · simpa [terminalSpan] using Over.w f.left
        · simpa [terminalSpan,content] using f.w
      · exact Subsingleton.elim _ _)

variable {A B}

/-- Instantiate the native product construction without imposing any product-preservation law on constant content. -/
noncomputable def spanProduct {I : Type w} {D : I → Spans A B} (G : Grades D)
    [HasPullback G.contextBody G.contentComparison] : Lift G :=
  ofPullback G _ (domainLift (pullback.fst G.contextBody G.contentComparison))
    (Iso.refl _) (by simp [domainLift]) (domain_cartesian _)

end ContextualComposition.NativeSpanProducts
