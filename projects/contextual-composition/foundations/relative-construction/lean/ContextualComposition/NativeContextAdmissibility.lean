module
public import ContextualComposition.NativeDependentPairFinite
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
@[expose] public section

/-! The manuscript's context restriction is a full subcategory on
admissible display projections, not a restriction on native carrier maps. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)

/-- The part of the class of display maps used by the native context
calculus: identities, isomorphisms, composition, and change of base. -/
structure NativeProjectionClass where
  admissible : {A B : Type u} → (A → B) → Prop
  ident (A : Type u) : admissible (id : A → A)
  equiv {A B : Type u} (e : A ≃ B) : admissible (e : A → B)
  comp {A B D : Type u} {f : A → B} {g : B → D} :
    admissible f → admissible g → admissible (g ∘ f)
  pullback {A B D : Type u} (f : A → D) (g : B → D) :
    admissible g → admissible (fun z : {ab : A × B // f ab.1 = g ab.2} => z.val.1)

def IndexedNativeFamily (A : Type u) (I : C) :=
  A → Aug (standardPush (C:=C)) I

namespace IndexedNativeFamily
variable {I : C} {A B : Type u}

noncomputable instance : Category (IndexedNativeFamily (C:=C) A I) where
  Hom F G := ∀ x : A, AugHom ℙ (F x) (G x)
  id F x := AugHom.ident (F x)
  comp f g x := (f x).comp (g x)
  id_comp f := funext fun x => AugHom.ident_comp (f x)
  comp_id f := funext fun x => AugHom.comp_ident (f x)
  assoc f g h := funext fun x => AugHom.comp_assoc (f x) (g x) (h x)

def Extension (P : IndexedNativeFamily (C:=C) A I) :=
  (x : A) × ULift.{u} (Fin (P x).base.n)

def projection (P : IndexedNativeFamily (C:=C) A I) : P.Extension → A := Sigma.fst

def reindex (P : IndexedNativeFamily (C:=C) A I) (f : B → A) : IndexedNativeFamily (C:=C) B I :=
  fun b => P (f b)

def reindexPullback (P : IndexedNativeFamily (C:=C) A I) (f : B → A) :
    (P.reindex f).Extension ≃ {bq : B × P.Extension // f bq.1 = P.projection bq.2} where
  toFun b := ⟨(b.1,⟨f b.1,b.2⟩),rfl⟩
  invFun := fun ⟨⟨b,⟨a,i⟩⟩,h⟩ =>
    ⟨b,cast (congrArg (fun x => ULift.{u} (Fin (P x).base.n)) h.symm) i⟩
  left_inv _ := rfl
  right_inv := by
    intro ⟨⟨b,⟨a,i⟩⟩,h⟩
    change f b = a at h
    subst a
    rfl

variable (J : NativeProjectionClass.{u})
def admissible : ObjectProperty (IndexedNativeFamily (C:=C) A I) :=
  fun P => J.admissible P.projection

abbrev Admissible := (admissible (C:=C) (I:=I) (A:=A) J).FullSubcategory

theorem reindex_admissible (P : IndexedNativeFamily (C:=C) A I) (h : admissible J P)
    (f : B → A) : admissible J (P.reindex f) := by
  have hh := J.comp (f:=(P.reindexPullback f : _ → _)) (g:=fun z => z.val.1)
    (J.equiv (P.reindexPullback f)) (J.pullback f P.projection h)
  exact hh

noncomputable def constantUnit : IndexedNativeFamily (C:=C) A I := fun _ => AugHom.unit I

noncomputable def unitExtensionEquiv : (constantUnit (C:=C) (I:=I) (A:=A)).Extension ≃ A where
  toFun := Sigma.fst
  invFun x := ⟨x,⟨(0 : Fin 1)⟩⟩
  left_inv := by
    intro ⟨x,⟨i⟩⟩
    have h : (i : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance i 0
    exact congrArg (fun j : Fin 1 => (⟨x,⟨j⟩⟩ : (constantUnit (C:=C) (I:=I) (A:=A)).Extension)) h.symm
  right_inv _ := rfl

theorem unit_admissible : admissible (C:=C) (I:=I) (A:=A) J constantUnit :=
  J.equiv unitExtensionEquiv

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (U : UnitCompat R I)

def pairAt (P : IndexedNativeFamily (C:=C) A I) (Q : IndexedNativeFamily (C:=C) P.Extension I)
    (x : A) : NativeDependentPair I :=
  ⟨P x,fun i => Q ⟨x,⟨i⟩⟩⟩

noncomputable def accumulate (P : IndexedNativeFamily (C:=C) A I) (Q : IndexedNativeFamily (C:=C) P.Extension I) :
    IndexedNativeFamily (C:=C) A I :=
  fun x => (P.pairAt Q x).accumulate R L U

noncomputable def accumulateExtension (P : IndexedNativeFamily (C:=C) A I)
    (Q : IndexedNativeFamily (C:=C) P.Extension I) :
    (P.accumulate R L U Q).Extension ≃ Q.Extension where
  toFun z :=
    let p := (P.pairAt Q z.1).readBranch R L U z.2.down
    ⟨⟨z.1,⟨p.1⟩⟩,⟨p.2⟩⟩
  invFun z :=
    ⟨z.1.1,⟨((P.pairAt Q z.1.1).readBranch R L U).symm ⟨z.1.2.down,z.2.down⟩⟩⟩
  left_inv := by
    intro ⟨x,⟨i⟩⟩
    exact congrArg (fun j => (⟨x,⟨j⟩⟩ : (P.accumulate R L U Q).Extension))
      (((P.pairAt Q x).readBranch R L U).symm_apply_apply i)
  right_inv := by
    intro ⟨⟨x,⟨i⟩⟩,⟨j⟩⟩
    exact congrArg (fun p : (P.pairAt Q x).Branch => (⟨⟨x,⟨p.1⟩⟩,⟨p.2⟩⟩ : Q.Extension))
      (((P.pairAt Q x).readBranch R L U).apply_symm_apply ⟨i,j⟩)

theorem accumulate_projection (P : IndexedNativeFamily (C:=C) A I)
    (Q : IndexedNativeFamily (C:=C) P.Extension I) :
    (P.accumulate R L U Q).projection = P.projection ∘ Q.projection ∘ P.accumulateExtension R L U Q :=
  rfl

theorem accumulate_admissible (P : IndexedNativeFamily (C:=C) A I) (Q : IndexedNativeFamily (C:=C) P.Extension I)
    (p : admissible J P) (q : admissible J Q) : admissible J (P.accumulate R L U Q) := by
  let f := P.accumulateExtension R L U Q
  have h := J.comp (f:=(f : _ → _)) (g:=Q.projection) (J.equiv f) q
  exact J.comp (f:=Q.projection ∘ f) (g:=P.projection) h p

/-- The independent product is indexed at the same base, not a product
of unrestricted extensions at unrelated base points. -/
noncomputable def tensor (P Q : IndexedNativeFamily (C:=C) A I) : IndexedNativeFamily (C:=C) A I :=
  fun x => independentAug R L (U.ρ I) (P x) (Q x)

noncomputable def tensorExtension (P Q : IndexedNativeFamily (C:=C) A I) :
    (tensor R L U P Q).Extension ≃ {z : P.Extension × Q.Extension // P.projection z.1 = Q.projection z.2} where
  toFun z :=
    let x := z.1
    let p := independentPairEquiv (P x).base (Q x).base z.2.down
    ⟨(⟨x,⟨p.1⟩⟩,⟨x,⟨p.2⟩⟩),rfl⟩
  invFun := fun ⟨⟨⟨x,⟨i⟩⟩,⟨y,⟨j⟩⟩⟩,h⟩ =>
    let j₀ := cast (congrArg (fun z => Fin (Q z).base.n) h.symm) j
    ⟨x,⟨(independentPairEquiv (P x).base (Q x).base).symm (i,j₀)⟩⟩
  left_inv := by
    intro ⟨x,⟨i⟩⟩
    exact congrArg (fun j => (⟨x,⟨j⟩⟩ : (tensor R L U P Q).Extension))
      ((independentPairEquiv (P x).base (Q x).base).symm_apply_apply i)
  right_inv := by
    intro ⟨⟨⟨x,⟨i⟩⟩,⟨y,⟨j⟩⟩⟩,h⟩
    change x = y at h
    subst y
    exact congrArg (fun k : Fin (P x).base.n × Fin (Q x).base.n =>
      (⟨(⟨x,⟨k.1⟩⟩,⟨x,⟨k.2⟩⟩),rfl⟩ :
        {z : P.Extension × Q.Extension // P.projection z.1 = Q.projection z.2}))
      ((independentPairEquiv (P x).base (Q x).base).apply_symm_apply (i,j))

theorem tensor_admissible (P Q : IndexedNativeFamily (C:=C) A I)
    (p : admissible J P) (q : admissible J Q) : admissible J (tensor R L U P Q) := by
  let e := tensorExtension R L U P Q
  let f := fun z : {z : P.Extension × Q.Extension // P.projection z.1 = Q.projection z.2} => z.val.1
  have h := J.comp (f:=(e : _ → _)) (g:=f) (J.equiv e) (J.pullback P.projection Q.projection q)
  exact J.comp (f:=f ∘ e) (g:=P.projection) h p

/-- Every native indexed map between the two admissible objects remains
a morphism. Display admissibility is not used on these carrier maps. -/
noncomputable def admitHom {P Q : Admissible (C:=C) (I:=I) (A:=A) J}
    (f : ∀ x, AugHom ℙ (P.obj x) (Q.obj x)) : P ⟶ Q :=
  ObjectProperty.homMk f

end IndexedNativeFamily
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
