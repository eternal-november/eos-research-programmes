module

public import ContextualComposition.FixedEffects
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

@[expose] public section

/-! The necessary direction of the discrete-context obstruction, on `Type u`.
Sources: issue #105, Discrete-transposition obstruction; Wreath-extension candidates, §8.
A small set is represented by a type and its maps by the actual maps of `Type u`.
The tags and representing objects are small in the same universe as the base. -/

namespace ContextualComposition.DiscreteTransposition
open CategoryTheory CategoryTheory.Limits
universe u

/-- The coproduct of the covariant representables at the types `D p`. -/
def polynomial (E : Type u) (D : E → Type u) : Type u ⥤ Type u where
  obj B := Σ p : E, D p → B
  map f := TypeCat.ofHom fun x => ⟨x.1, fun d => f (x.2 d)⟩
  map_id B := by
    apply ConcreteCategory.hom_ext
    rintro ⟨p, h⟩
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- Discrete pure postcomposition leaves the context tag fixed. -/
theorem polynomial_map {E : Type u} (D : E → Type u) {B C : Type u}
    (f : B ⟶ C) (p : E) (h : D p → B) :
    (polynomial E D).map f ⟨p, h⟩ = ⟨p, fun d => f (h d)⟩ := rfl

/-- Postcomposition with the actual pure Kleisli lift of a base arrow.
`MonadRecovery.kleisli_comp` identifies the composition here with native Kleisli composition. -/
theorem purePost_eq_map (T : CategoryTheory.Monad (Type u))
    {A B C : Type u} (k : MonadRecovery.Arrow T A B) (f : B ⟶ C) :
    MonadRecovery.comp T k (MonadRecovery.pure T f) = k ≫ T.map f := by
  simp only [MonadRecovery.comp, MonadRecovery.pure, Functor.map_comp, Category.assoc,
    Monad.right_unit]
  change k ≫ T.map f ≫ 𝟙 (T.obj C) = _
  rw [Category.comp_id]

/-- The hom-level data forced by the given transposition. The law compares native pure
postcomposition with tag-preserving postcomposition, not with a transported action. -/
structure Presentation (T : CategoryTheory.Monad (Type u)) where
  grades : Type u → Type u
  dom : (A : Type u) → grades A → Type u
  homEquiv : ∀ A B, MonadRecovery.Arrow T A B ≃ (polynomial (grades A) (dom A)).obj B
  purePost : ∀ {A B C : Type u} (k : MonadRecovery.Arrow T A B) (f : B ⟶ C),
    homEquiv A C (MonadRecovery.comp T k (MonadRecovery.pure T f)) =
      (polynomial (grades A) (dom A)).map f (homEquiv A B k)

/-- Naturality in the codomain for every source, derived from the pure comparison law. -/
theorem Presentation.homEquiv_natural {T : CategoryTheory.Monad (Type u)} (S : Presentation T)
    {A B C : Type u} (k : MonadRecovery.Arrow T A B) (f : B ⟶ C) :
    S.homEquiv A C (k ≫ T.map f) =
      (polynomial (S.grades A) (S.dom A)).map f (S.homEquiv A B k) := by
  rw [← purePost_eq_map]
  exact S.purePost k f

/-- Evaluation at the unique point of the small singleton, with constant-function inverse. -/
def singletonEval (B : Type u) : (PUnit.{u+1} ⟶ B) ≃ B where
  toFun k := k PUnit.unit
  invFun b := TypeCat.ofHom fun _ => b
  left_inv k := by
    ext z
    cases z
    rfl
  right_inv _ := rfl

/-- The singleton extraction is a natural isomorphism of the actual Type endofunctors. -/
def Presentation.singletonIso {T : CategoryTheory.Monad (Type u)} (S : Presentation T) :
    T.toFunctor ≅ polynomial (S.grades PUnit.{u+1}) (S.dom PUnit.{u+1}) :=
  NatIso.ofComponents
    (fun B => ((singletonEval (T.obj B)).symm.trans (S.homEquiv PUnit B)).toIso)
    (by
      intro B C f
      ext b
      let k : MonadRecovery.Arrow T PUnit B := (singletonEval (T.obj B)).symm b
      exact S.homEquiv_natural k f)

/-- Target is the concrete Type pullback of the two mapped legs. -/
abbrev MappedPullback (F : Type u ⥤ Type u) {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Types.PullbackObj (F.map f) (F.map g)

/-- The image of the explicit limit cone, with the functor applied to its actual projections. -/
def imageCone (F : Type u ⥤ Type u) {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PullbackCone (F.map f) (F.map g) :=
  let c := Types.pullbackCone f g
  PullbackCone.mk (F.map c.fst) (F.map c.snd) (by
    rw [← F.map_comp, ← F.map_comp, c.condition])

/-- The actual canonical map from the image apex to the pullback of the mapped cospan. -/
def comparison (F : Type u ⥤ Type u) {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    F.obj (Types.PullbackObj f g) → MappedPullback F f g :=
  (imageCone F f g).toPullbackObj

/-- Matched tags give a common representing object. Equality of the mapped functions then
allows forming the pullback point separately at every element of that object. -/
theorem polynomial_comparison_bijective (E : Type u) (D : E → Type u)
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Function.Bijective (comparison (polynomial E D) f g) := by
  constructor
  · rintro ⟨p, a⟩ ⟨q, b⟩ h
    have h₁ : (⟨p, fun d => (a d).1.1⟩ : Σ p, D p → X) = ⟨q, fun d => (b d).1.1⟩ :=
      congrArg (fun x => x.1.1) h
    have h₂ : (⟨p, fun d => (a d).1.2⟩ : Σ p, D p → Y) = ⟨q, fun d => (b d).1.2⟩ :=
      congrArg (fun x => x.1.2) h
    have hpq : p = q := congrArg Sigma.fst h₁
    subst q
    have e₁ := sigma_mk_injective h₁
    have e₂ := sigma_mk_injective h₂
    congr 1
    funext d
    exact Subtype.ext (Prod.ext (congrFun e₁ d) (congrFun e₂ d))
  · rintro ⟨⟨⟨p, a⟩, ⟨q, b⟩⟩, h⟩
    have hpq : p = q := congrArg Sigma.fst h
    subst q
    have e : (fun d => f (a d)) = (fun d => g (b d)) := sigma_mk_injective h
    exact ⟨⟨p, fun d => ⟨(a d, b d), congrFun e d⟩⟩, rfl⟩

private def targetMap {F G : Type u ⥤ Type u} (e : F ⟶ G)
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    MappedPullback F f g → MappedPullback G f g := fun y =>
  ⟨(e.app X y.1.1, e.app Y y.1.2), by
    change G.map f (e.app X y.1.1) = G.map g (e.app Y y.1.2)
    exact (ConcreteCategory.congr_hom (e.naturality f) y.1.1).symm.trans
      ((congrArg (fun z => e.app Z z) y.2).trans
        (ConcreteCategory.congr_hom (e.naturality g) y.1.2))⟩

private theorem targetMap_injective {F G : Type u ⥤ Type u} (e : F ≅ G)
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Function.Injective (targetMap e.hom f g) := by
  intro x y h
  exact Subtype.ext (Prod.ext ((e.app X).toEquiv.injective (congrArg (fun q => q.1.1) h))
    ((e.app Y).toEquiv.injective (congrArg (fun q => q.1.2) h)))

private theorem comparison_natural {F G : Type u ⥤ Type u} (e : F ⟶ G)
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) (a : F.obj (Types.PullbackObj f g)) :
    targetMap e f g (comparison F f g a) =
      comparison G f g (e.app (Types.PullbackObj f g) a) := by
  apply Subtype.ext
  apply Prod.ext
  · let proj := (Types.pullbackCone f g).fst
    change e.app X (F.map proj a) = G.map proj (e.app (Types.PullbackObj f g) a)
    exact ConcreteCategory.congr_hom (e.naturality proj) a
  · let proj := (Types.pullbackCone f g).snd
    change e.app Y (F.map proj a) = G.map proj (e.app (Types.PullbackObj f g) a)
    exact ConcreteCategory.congr_hom (e.naturality proj) a

/-- Transport the bijectivity of the comparisons across a natural isomorphism. -/
theorem comparison_bijective_of_iso {F G : Type u ⥤ Type u} (e : F ≅ G)
    {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Function.Bijective (comparison G f g)) : Function.Bijective (comparison F f g) := by
  let eqv := (e.app (Types.PullbackObj f g)).toEquiv
  constructor
  · intro a b hab
    apply eqv.injective
    apply h.injective
    change comparison G f g (e.hom.app _ a) = comparison G f g (e.hom.app _ b)
    rw [← comparison_natural e.hom f g a, ← comparison_natural e.hom f g b, hab]
  · intro y
    obtain ⟨b, hb⟩ := h.surjective (targetMap e.hom f g y)
    obtain ⟨a, ha⟩ := eqv.surjective b
    refine ⟨a, targetMap_injective e f g ?_⟩
    rw [comparison_natural, show e.hom.app (Types.PullbackObj f g) a = b from ha, hb]

/-- The necessary test for the original monad: all canonical cospan comparisons are bijective. -/
theorem Presentation.comparison_bijective {T : CategoryTheory.Monad (Type u)}
    (S : Presentation T) {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Function.Bijective (comparison T.toFunctor f g) :=
  comparison_bijective_of_iso S.singletonIso f g (polynomial_comparison_bijective _ _ f g)

/-- Categorical version: applying the functor to the explicit Type pullback cone is limiting.
Every pullback cone on this cospan is isomorphic to the explicit one when it is limiting. -/
noncomputable def Presentation.imageConeIsLimit {T : CategoryTheory.Monad (Type u)}
    (S : Presentation T) {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (imageCone T.toFunctor f g) :=
  (imageCone T.toFunctor f g).isLimitEquivBijective.symm (S.comparison_bijective f g)

end ContextualComposition.DiscreteTransposition
