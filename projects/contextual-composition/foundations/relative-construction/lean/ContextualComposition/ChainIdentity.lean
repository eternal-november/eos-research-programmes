module
public import ContextualComposition.NativeSuccessor
@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeSquares
open CategoryTheory Opposite
universe b w u v
variable {B : Type b} [Category.{w} B] {P : Endpoints.{b,w,u,v} B} (Y : Bᵒᵖ ⥤ Cat.{v,u}) (S : P.Split)

def nativeId {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Cat.{v,u}) {A : C} (x : F.obj (op A)) :
    x ⟶ (F.map (𝟙 A).op).toFunctor.obj x :=
  eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (F.map_id (op A))) x).symm

private theorem alignedTransport {C : Type*} [Category* C] {x y : C} (h : x = y) :
    Aligned (eqToHom h) (𝟙 x) := by subst y; exact Aligned.refl _

private theorem gradeTransport {K : Type*} [Category* K] {e : K ⥤ B} {x y : Total Y e} (h : x = y) :
    Aligned (gradeMap (eqToHom h)) (𝟙 (grade Y e x)) := by subst y; exact Aligned.refl _

set_option backward.isDefEq.respectTransparency false in
private theorem payloadTransport {K : Type*} [Category* K] {e : K ⥤ B} {x y : Total Y e} (h : x = y) :
    Aligned (payloadMap (eqToHom h)) (𝟙 (payload Y e x)) := by
  subst y
  change Aligned ((Grothendieck.Hom.fiber (𝟙 x.unop)).unop) _
  rw [Grothendieck.id_fiber,eqToHom_unop]
  exact alignedTransport _

set_option backward.isDefEq.respectTransparency false in
theorem tail_identity {n A} (p : P.grades.obj (op A)) (t : Chain P n ((P.extend A).obj p))
    (x : Y.obj (op (endpoint t))) :
    tailPart Y (decoratedId S Y (.cons p t) x) =
      rebaseDecorated Y (next_id S p).symm (decoratedId S Y t x) := by
  rw [rebaseDecorated_data]
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  dsimp only [tailPart,decoratedId]
  rw [eqToHom_trans]

private theorem extAligned {K : Type*} [Category* K] {e : K ⥤ B}
    {x y : Total Y e} {f g : x ⟶ y} (head : gradeMap f = gradeMap g)
    (tail : Aligned (payloadMap f) (payloadMap g)) : f = g := by
  apply (homEquiv x y).injective
  refine Sigma.ext head ?_
  have aux {k j : grade Y e x ⟶ grade Y e y}
      {m : payload Y e x ⟶ (Y.map (e.map k).op).toFunctor.obj (payload Y e y)}
      {l : payload Y e x ⟶ (Y.map (e.map j).op).toFunctor.obj (payload Y e y)}
      (hk : k = j) (hh : Aligned m l) : HEq m l := by
    subst j; exact heq_of_eq hh.eq
  exact aux head tail

set_option backward.isDefEq.respectTransparency false in
theorem square_id_native : {n : Nat} → {A : B} → (t : Chain P n A) →
    (x : Y.obj (op (endpoint t))) →
    squareEquiv Y S (𝟙 A) t t x x (decoratedId S Y t x) =
      nativeId (Iterates.layer P S Y n) (realize Y S t x)
  | 0, _, .nil _, _ => rfl
  | n+1, A, .cons p t, x => by
    let F := Iterates.layer P S Y n
    apply extAligned F (e := P.extend A)
    · apply Aligned.eq
      apply Aligned.trans _ (gradeTransport F _).symm
      change Aligned (headId (P := P) p) (𝟙 p)
      exact alignedTransport _
    · apply Aligned.trans _ (payloadTransport F _).symm
      rw [compared_tail]
      apply (Aligned.trailing _ _).trans
      change Aligned (squareEquiv Y S _ t t x x (tailPart Y (decoratedId S Y (.cons p t) x))) _
      rw [tail_identity,comparison_rebase]
      apply (Aligned.trailing _ _).trans
      rw [square_id_native t x]
      exact alignedTransport _

section Units
variable {C : Type*} [Category* C] (F : Cᵒᵖ ⥤ Cat.{v,u})
    {A D : C} {a : A ⟶ D} {x : F.obj (op A)} {y : F.obj (op D)}
    (f : x ⟶ (F.map a.op).toFunctor.obj y)

set_option backward.isDefEq.respectTransparency false in
theorem native_left_unit : Aligned (nativePaste F (a := 𝟙 A) (b := a) (x := x) (y := x) (z := y)
    (nativeId F x) f) f := by
  apply (native_reduced F _ _).trans
  have h : Aligned ((F.map (𝟙 A).op).toFunctor.map f) f := by
    rw [op_id,F.map_id]; exact Aligned.refl _
  conv_rhs => rw [← Category.id_comp f]
  apply Aligned.comp (alignedTransport _) h

set_option backward.isDefEq.respectTransparency false in
theorem native_right_unit : Aligned (nativePaste F (a := a) (b := 𝟙 D) (x := x) (y := y) (z := y)
    f (nativeId F y)) f := by
  apply (native_reduced F _ _).trans
  conv_rhs => rw [← Category.comp_id f]
  apply (Aligned.refl f).comp
  rw [← (F.map a.op).toFunctor.map_id y]
  apply Aligned.map
  exact alignedTransport _
end Units

set_option backward.isDefEq.respectTransparency false in
theorem decorated_left_unit {n A D} {a : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))} (f : DecoratedHom Y a t z x y) :
    rebaseDecorated Y (Category.id_comp a) (decoratedComp S Y (decoratedId S Y t x) f) = f := by
  apply (squareEquiv Y S _ _ _ _ _).injective
  rw [comparison_rebase]
  apply Aligned.eq
  apply (Aligned.trailing _ _).trans
  rw [square_comp_native,square_id_native]
  apply native_left_unit

set_option backward.isDefEq.respectTransparency false in
theorem decorated_right_unit {n A D} {a : A ⟶ D} {t : Chain P n A} {z : Chain P n D}
    {x : Y.obj (op (endpoint t))} {y : Y.obj (op (endpoint z))} (f : DecoratedHom Y a t z x y) :
    rebaseDecorated Y (Category.comp_id a) (decoratedComp S Y f (decoratedId S Y z y)) = f := by
  apply (squareEquiv Y S _ _ _ _ _).injective
  rw [comparison_rebase]
  apply Aligned.eq
  apply (Aligned.trailing _ _).trans
  rw [square_comp_native,square_id_native]
  apply native_right_unit


/-- The fixed-length source fibre, defined without using the realization. -/
structure Fibre (P : Endpoints.{b,w,u,v} B) (Y : Bᵒᵖ ⥤ Cat.{v,u}) (n : Nat) (A : B) where
  chain : Chain P n A
  value : Y.obj (op (endpoint chain))

namespace Fibre
variable {n : Nat} {A : B} {Y}
def Hom (X Z : Fibre P Y n A) := DecoratedHom Y (𝟙 A) X.chain Z.chain X.value Z.value
def ident (X : Fibre P Y n A) : Hom X X := decoratedId S Y X.chain X.value
def paste {X Z W : Fibre P Y n A} (f : Hom X Z) (g : Hom Z W) : Hom X W :=
  rebaseDecorated Y (Category.id_comp (𝟙 A)) (decoratedComp S Y f g)

def obj (X : Fibre P Y n A) := realize Y S X.chain X.value
def homComparison (X Z : Fibre P Y n A) : Hom X Z ≃ (obj S X ⟶ obj S Z) :=
  verticalEquiv Y S X.chain Z.chain X.value Z.value

private theorem homAligned {X Z : Fibre P Y n A} (f : Hom X Z) :
    Aligned (homComparison S X Z f) (squareEquiv Y S _ _ _ _ _ f) := by
  have cast' {C : Type u} [Category.{v} C] {x d e : C} (h : d = e) (m : x ⟶ d) :
      Aligned (Equiv.cast (congrArg (fun dest => x ⟶ dest) h) m) m := by
    subst e; exact Aligned.refl _
  exact cast' (Functor.congr_obj (congrArg Cat.Hom.toFunctor ((Iterates.layer P S Y n).map_id (op A))) (obj S Z)) _

theorem ident_comparison (X : Fibre P Y n A) : homComparison S X X (ident S X) = 𝟙 (obj S X) := by
  apply Aligned.eq
  apply (homAligned S _).trans
  unfold ident
  rw [square_id_native]
  exact alignedTransport _

set_option backward.isDefEq.respectTransparency false in
theorem paste_comparison {X Z W : Fibre P Y n A} (f : Hom X Z) (g : Hom Z W) :
    homComparison S X W (paste S f g) = homComparison S X Z f ≫ homComparison S Z W g := by
  apply Aligned.eq
  apply (homAligned S _).trans
  unfold paste
  rw [comparison_rebase]
  apply (Aligned.trailing _ _).trans
  rw [square_comp_native]
  apply (native_reduced _ _ _).trans
  apply Aligned.comp (homAligned S f).symm
  have mapId (F : Bᵒᵖ ⥤ Cat.{v,u}) {p q : F.obj (op A)} (m : p ⟶ q) :
      Aligned ((F.map (𝟙 A).op).toFunctor.map m) m := by
    rw [op_id,F.map_id]; exact Aligned.refl _
  exact (mapId _ _).trans (homAligned S g).symm

/-- The category uses the original independent operations. The faithful comparison
proves their laws; it does not define either operation. -/
@[instance_reducible] def category : Category (Fibre P Y n A) where
  Hom := Hom
  id := ident S
  comp := paste S
  id_comp f := (homComparison S _ _).injective (by rw [paste_comparison,ident_comparison,Category.id_comp])
  comp_id f := (homComparison S _ _).injective (by rw [paste_comparison,ident_comparison,Category.comp_id])
  assoc f g h := (homComparison S _ _).injective (by simp only [paste_comparison,Category.assoc])

def asCat (n : Nat) (A : B) := @Cat.of (Fibre P Y n A) (category S)

def comparison (n : Nat) (A : B) :
    asCat (Y := Y) S n A ⥤ (Iterates.layer P S Y n).obj (op A) where
  obj X := obj S X
  map {X Z} f := homComparison S X Z f
  map_id X := ident_comparison S X
  map_comp f g := paste_comparison S f g

instance comparisonFull : (comparison (Y := Y) S n A).Full where
  map_surjective {X Z} f := ⟨(homComparison S X Z).symm f,(homComparison S X Z).apply_symm_apply _⟩

instance comparisonFaithful : (comparison (Y := Y) S n A).Faithful where
  map_injective {X Z} := (homComparison S X Z).injective

instance comparisonEssSurj : (comparison (Y := Y) S n A).EssSurj where
  mem_essImage z :=
    let d := unrealize Y S n A z
    ⟨(⟨d.1,d.2⟩ : Fibre P Y n A),⟨eqToIso (pack_unpack Y S n A z)⟩⟩

instance comparisonIsEquivalence : (comparison (Y := Y) S n A).IsEquivalence where

noncomputable def equivalence (n : Nat) (A : B) :
    asCat (Y := Y) S n A ≌ (Iterates.layer P S Y n).obj (op A) :=
  (comparison S n A).asEquivalence
abbrev All (A : B) := Σ n, (asCat (Y := Y) S n A : Type _)

def allComparison (A : B) : All (Y := Y) S A ⥤ Iterates.Packed P S Y (op A) :=
  Sigma.desc (C := fun n => (asCat (Y := Y) S n A : Type _)) fun n => comparison S n A ⋙ Sigma.incl (C := fun i => ((Iterates.layer P S Y i).obj (op A) : Type u)) n

instance allFull : (allComparison (Y := Y) S A).Full where
  map_surjective := by
    rintro ⟨n,X⟩ ⟨m,Z⟩ f
    change Sigma.SigmaHom (C := fun i => ((Iterates.layer P S Y i).obj (op A) : Type u)) ⟨n,_⟩ ⟨m,_⟩ at f
    cases f with
    | mk f =>
      refine ⟨Sigma.SigmaHom.mk ((homComparison S X Z).symm f),?_⟩
      exact congrArg Sigma.SigmaHom.mk ((homComparison S X Z).apply_symm_apply f)

instance allFaithful : (allComparison (Y := Y) S A).Faithful where
  map_injective := by
    rintro ⟨n,X⟩ ⟨m,Z⟩ f g h
    cases f with
    | mk f =>
      cases g with
      | mk g =>
        change Sigma.SigmaHom.mk (C := fun i => ((Iterates.layer P S Y i).obj (op A) : Type u)) (i := n) ((homComparison S _ _) f) = Sigma.SigmaHom.mk (C := fun i => ((Iterates.layer P S Y i).obj (op A) : Type u)) (i := n) ((homComparison S _ _) g) at h
        injection h with _ _ _ hh
        exact congrArg Sigma.SigmaHom.mk ((homComparison S _ _).injective hh)

instance allEssSurj : (allComparison (Y := Y) S A).EssSurj where
  mem_essImage := by
    rintro ⟨n,z⟩
    let d := unrealize Y S n A z
    refine ⟨⟨n,(⟨d.1,d.2⟩ : Fibre P Y n A)⟩,⟨eqToIso ?_⟩⟩
    exact congrArg (fun v => (⟨n,v⟩ : Iterates.Packed P S Y (op A))) (pack_unpack Y S n A z)

instance allIsEquivalence : (allComparison (Y := Y) S A).IsEquivalence where

noncomputable def allEquivalence (A : B) :
    All (Y := Y) S A ≌ Iterates.Packed P S Y (op A) := (allComparison S A).asEquivalence
end Fibre
end ContextualComposition.GrothendieckStep.TelescopeSquares
