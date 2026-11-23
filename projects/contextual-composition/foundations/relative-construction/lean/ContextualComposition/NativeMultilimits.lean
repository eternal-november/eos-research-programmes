module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! The natural disjoint union of full factorization homs for a diagram in a category of elements. For native witnesses and coefficients the base is the family category of the coefficient category, and the element is the supplied effect on its raw indexing set. -/

@[expose] public section
namespace ContextualComposition.NativeMultilimits

open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u j k
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
  {J : Type j} [Category.{k} J] (D : J ⥤ F.Elements)

abbrev Base := D ⋙ Functor.Elements.π F
abbrev FixedCone {E : Type*} [Category* E] (d : J ⥤ E) (A : E) := (Functor.const J).obj A ⟶ d

variable (s : Cone (Base F D))

abbrev Index := {t : F.obj s.pt // ∀ i, F.map (s.π.app i) t = (D.obj i).val}
abbrev joint (t : Index F D s) : F.Elements := F.elementsMk s.pt t.val

def projection (t : Index F D s) : FixedCone D (joint F D s t) where
  app i := Functor.Elements.homMk (s.π.app i) (t.property i)
  naturality i i' f := by apply Functor.Elements.hom_ext; exact (Category.id_comp _).trans (s.w f).symm

def forgetCone (A : F.Elements) (c : FixedCone D A) : Cone (Base F D) where
  pt := A.obj
  π := {
    app := fun i => (c.app i).hom
    naturality := fun _ _ f => congrArg (fun r => Functor.Elements.Hom.hom r) (c.naturality f) }

variable (lim : IsLimit s)

def index (A : F.Elements) (c : FixedCone D A) : Index F D s :=
  ⟨F.map (lim.lift (forgetCone F D A c)) A.val, fun i => by
    let r : A.obj ⟶ s.pt := lim.lift (forgetCone F D A c)
    exact (congrArg (fun f : F.obj A.obj ⟶ F.obj (D.obj i).obj => f A.val) (F.map_comp r (s.π.app i))).symm.trans
      ((congrArg (fun f : A.obj ⟶ (D.obj i).obj => F.map f A.val) (lim.fac (forgetCone F D A c) i)).trans (c.app i).map_val)⟩

def factor (A : F.Elements) (c : FixedCone D A) : Σ t : Index F D s, A ⟶ joint F D s t :=
  ⟨index F D s lim A c,Functor.Elements.homMk (lim.lift (forgetCone F D A c)) rfl⟩

def present (A : F.Elements) (m : Σ t : Index F D s, A ⟶ joint F D s t) : FixedCone D A :=
  (Functor.const J).map m.2 ≫ projection F D s m.1

theorem factor_ext (A : F.Elements) {x y : Σ t : Index F D s, A ⟶ joint F D s t}
    (eq : x.2.hom = y.2.hom) : x = y := by
  rcases x with ⟨x,f⟩
  rcases y with ⟨y,g⟩
  have e : x = y := Subtype.ext (f.map_val.symm.trans ((congrArg (fun h => F.map h A.val) eq).trans g.map_val))
  cases e
  exact congrArg (Sigma.mk x) (Functor.Elements.hom_ext eq)

/-- The whole coefficient morphism is forced by the base limit; preservation of the effect then forces its component index. -/
def multilimit (A : F.Elements) : (Σ t : Index F D s, A ⟶ joint F D s t) ≃ FixedCone D A where
  toFun := present F D s A
  invFun := factor F D s lim A
  left_inv m := by
    apply factor_ext
    apply lim.hom_ext
    intro i
    exact lim.fac (forgetCone F D A (present F D s A m)) i
  right_inv c := by
    apply NatTrans.ext; funext i
    apply Functor.Elements.hom_ext
    exact lim.fac (forgetCone F D A c) i

theorem factor_natural {A A' : F.Elements} (h : A' ⟶ A) (c : FixedCone D A) :
    factor F D s lim A' ((Functor.const J).map h ≫ c) =
    ⟨(factor F D s lim A c).1,h ≫ (factor F D s lim A c).2⟩ := by
  apply factor_ext
  apply lim.hom_ext
  intro i
  exact (lim.fac (forgetCone F D A' ((Functor.const J).map h ≫ c)) i).trans
    ((Category.assoc h.hom (lim.lift (forgetCone F D A c)) _).trans
      (congrArg (h.hom ≫ ·) (lim.fac (forgetCone F D A c) i))).symm

include lim in
theorem no_index_no_cone (empty : IsEmpty (Index F D s)) (A : F.Elements) : IsEmpty (FixedCone D A) :=
  ⟨fun c => empty.false (index F D s lim A c)⟩

def family : FormalCoproduct.{w} F.Elements := ⟨Index F D s,joint F D s⟩

/-- For the empty diagram every effect on the base terminal object is a separate index. -/
def emptyIndex [IsEmpty J] : Index F D s ≃ F.obj s.pt where
  toFun := Subtype.val
  invFun t := ⟨t,fun i => isEmptyElim i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Even an empty finite diagram can have arbitrarily many native indices: a constant effect functor gives exactly its supplied small set. -/
def constantEmptyIndex (X : Type w) (D : J ⥤ ((Functor.const C).obj X).Elements)
    (s : Cone (Base ((Functor.const C).obj X) D)) [IsEmpty J] :
    Index ((Functor.const C).obj X) D s ≃ X := emptyIndex _ _ _

/-- The raw-index functor retains every witness; its source morphisms also carry every coefficient map. -/
def raw (V : Type u) [Category.{v} V] : FormalCoproduct.{w} V ⥤ Type w where
  obj P := P.I
  map f := TypeCat.ofHom f.f

abbrev Native (T : Type w ⥤ Type w) (V : Type u) [Category.{v} V] := (raw V ⋙ T).Elements

def nativeMk (T : Type w ⥤ Type w) {V : Type u} [Category.{v} V]
    (W : Type w) (p : T.obj W) (coeff : W → V) : Native T V :=
  (raw V ⋙ T).elementsMk ⟨W,coeff⟩ p

def nativeHom (T : Type w ⥤ Type w) {V : Type u} [Category.{v} V] (P Q : Native T V)
    (f : P.obj.I → Q.obj.I) (h : T.map (TypeCat.ofHom f) P.val = Q.val)
    (α : ∀ w, P.obj.obj w ⟶ Q.obj.obj (f w)) : P ⟶ Q := Functor.Elements.homMk ⟨f,α⟩ h

def singletonFullyFaithful (T : Type w ⥤ Type w) (V : Type u) [Category.{v} V] :
    (FormalCoproduct.incl.{w} (Native T V)).FullyFaithful := FormalCoproduct.fullyFaithfulIncl

end ContextualComposition.NativeMultilimits
