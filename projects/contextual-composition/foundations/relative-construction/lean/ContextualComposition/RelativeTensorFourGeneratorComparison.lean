module
public import ContextualComposition.RelativeTensorFourNative
public import Mathlib.CategoryTheory.Products.Associator

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated
open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

section General
variable {S T : Type*} [Category* S] [Category* T] {H K : S ⥤ T}

/-- Naturality of the proposed object comparison at a single specified arrow. -/
abbrev CompareAt (p : ∀ x, H.obj x ≅ K.obj x) {x y : S} (a : x ⟶ y) : Prop :=
  H.map a ≫ (p y).hom = (p x).hom ≫ K.map a

private theorem compareComp (p : ∀ x, H.obj x ≅ K.obj x) {x y z : S} (f : x ⟶ y) (g : y ⟶ z)
    (hf : CompareAt p f) (hg : CompareAt p g) : CompareAt p (f ≫ g) := by
  unfold CompareAt at *
  rw [H.map_comp,K.map_comp,Category.assoc,hg,← Category.assoc,hf,Category.assoc]

universe vF uF vG uG
variable {B E : Type*} [Category* B] [Category* E]
variable {F : LocallyDiscrete B ⥤ᵖ Cat.{vF,uF}} {G : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vG,uG}}

/-- Naturality on tensor generators with a simultaneous parameter arrow extends to all arrows of the tensor times the parameter category. -/
theorem tensorParameterComparison (J : (Tensor F G × E) ⥤ S) (p : ∀ x, H.obj x ≅ K.obj x)
    (native : ∀ {b : B} {x x' : F.obj ⟨b⟩} {y y' : G.obj ⟨op b⟩} {e e' : E}
      (f : x ⟶ x') (g : y ⟶ y') (h : e ⟶ e'),
      CompareAt p (J.map (productMap ((insertion F G b).map (productMap f g)) h)))
    (balance : ∀ {a b : B} (u : a ⟶ b) (x : F.obj ⟨a⟩) (y : G.obj ⟨op b⟩) (e : E),
      CompareAt p (J.map (productMap (balancing F G u x y).hom (𝟙 e))))
    {z z' : Tensor F G} {e e' : E} (f : z ⟶ z') (g : e ⟶ e') :
    CompareAt p (J.map (productMap f g)) := by
  let I := CategoryTheory.Prod.sectL (Tensor F G) e ⋙ J
  let i : (I ⋙ H) ≅ (I ⋙ K) := isoOfGenerators (fun z => p (I.obj z))
    (fun f g => native f g (𝟙 e)) (fun u x y => balance u x y e)
  have left : CompareAt p (J.map (productMap f (𝟙 e))) := i.hom.naturality f
  have right : CompareAt p (J.map (productMap (𝟙 z') g)) := by
    obtain ⟨⟨b,x,y⟩⟩ := z'
    have h := native (𝟙 x) (𝟙 y) g
    change CompareAt p (J.map (productMap ((insertion F G b).map (𝟙 (x,y))) g)) at h
    rw [Functor.map_id] at h
    exact h
  have split : productMap f g = productMap f (𝟙 e) ≫ productMap (𝟙 z') g :=
    Prod.ext (Category.comp_id _).symm (Category.id_comp _).symm
  rw [split,Functor.map_comp]
  exact compareComp p _ _ left right
end General

section Four
universe vB uB vC uC vD uD vX uX vM uM vN uN vY uY
variable {B : Type uB} {C : Type uC} {D : Type uD} [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX})
variable (M : LocallyDiscrete C ⥤ᵖ (LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vM,uM}))
variable (N : LocallyDiscrete D ⥤ᵖ (LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vN,uN}))
variable (Y : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vY,uY})
variable {T : Type*} [Category* T] {H K : farLeft X M N Y ⥤ T}

/-- The innermost balance in the far-left carrier with both untouched payloads carried by identities. -/
abbrev farLeftBalanceB {a b : B} {c : C} {d : D} (u : a ⟶ b) (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩)
    (n : (column N d).obj ⟨op c⟩) (y : Y.obj ⟨op d⟩) :=
  (Reverse.insertL (leftInner X M) N Y d).map (productMap ((insertion (leftInner X M) (column N d) c).map
    (productMap (balancing X (column M c) u x m).hom (𝟙 n))) (𝟙 y))

/-- The second junction balance inserted into the outermost tensor. -/
abbrev farLeftBalanceC {c c' : C} {d : D} (v : c ⟶ c') (z : Tensor X (column M c)) (n : (column N d).obj ⟨op c'⟩) (y : Y.obj ⟨op d⟩) :=
  (Reverse.insertL (leftInner X M) N Y d).map (productMap (balancing (leftInner X M) (column N d) v z n).hom (𝟙 y))

/-- The outermost junction balance of the original four-factor carrier. -/
abbrev farLeftBalanceD {d e : D} (w : d ⟶ e) (z : Tensor (leftInner X M) (column N d)) (y : Y.obj ⟨op e⟩) :=
  (balancing (leftInner (leftInner X M) N) Y w z y).hom

/-- Naturality tests for the simultaneous native arrows and the three forward junction balances. Inner tensor arguments of the balance tests are objects. -/
structure FourGeneratorLaws (p : ∀ z, H.obj z ≅ K.obj z) : Prop where
  native {b : B} {c : C} {d : D} {x x' : X.obj ⟨b⟩} {m m' : (column M c).obj ⟨op b⟩}
    {n n' : (column N d).obj ⟨op c⟩} {y y' : Y.obj ⟨op d⟩} (f : x ⟶ x') (g : m ⟶ m') (h : n ⟶ n') (i : y ⟶ y') :
    CompareAt p (leftFourNative X M N Y f g h i)
  balanceB {a b : B} {c : C} {d : D} (u : a ⟶ b) (x : X.obj ⟨a⟩) (m : (column M c).obj ⟨op b⟩)
    (n : (column N d).obj ⟨op c⟩) (y : Y.obj ⟨op d⟩) : CompareAt p (farLeftBalanceB X M N Y u x m n y)
  balanceC {c c' : C} {d : D} (v : c ⟶ c') (z : Tensor X (column M c)) (n : (column N d).obj ⟨op c'⟩)
    (y : Y.obj ⟨op d⟩) : CompareAt p (farLeftBalanceC X M N Y v z n y)
  balanceD {d e : D} (w : d ⟶ e) (z : Tensor (leftInner X M) (column N d)) (y : Y.obj ⟨op e⟩) :
    CompareAt p (farLeftBalanceD X M N Y w z y)

variable (p : ∀ z, H.obj z ≅ K.obj z)

/-- The generator tests suffice for the outer native insertion with an arbitrary inner quotient arrow. -/
theorem fourOuterNative (h : FourGeneratorLaws X M N Y p) {d : D} {z z' : Tensor (leftInner X M) (column N d)}
    {y y' : Y.obj ⟨op d⟩} (f : z ⟶ z') (g : y ⟶ y') :
    CompareAt p ((Reverse.insertL (leftInner X M) N Y d).map (productMap f g)) := by
  let O := Reverse.insertL (leftInner X M) N Y d
  apply tensorParameterComparison (F := leftInner X M) (G := column N d) O p ?_ ?_ f g
  · intro c z z' n n' y y' r a i
    let J := prod.inverseAssociator (Tensor X (column M c)) ((column N d).obj ⟨op c⟩) (Y.obj ⟨op d⟩) ⋙
      ((insertion (leftInner X M) (column N d) c).prod (𝟭 _)) ⋙ O
    apply tensorParameterComparison (F := X) (G := column M c) J p ?_ ?_ r (productMap a i)
    · intro b x x' m m' ny ny' fx fm fny
      exact h.native fx fm fny.1 fny.2
    · intro a b u x m ny
      exact h.balanceB u x m ny.1 ny.2
  · intro c c' v z n y
    exact h.balanceC v z n y

/-- The proposed object isomorphisms give a natural isomorphism on the full localized four-factor tensor. -/
def isoOfFourGenerators (h : FourGeneratorLaws X M N Y p) : H ≅ K :=
  isoOfGenerators p (fun f g => fourOuterNative X M N Y p h f g) (fun w x y => h.balanceD w x y)

@[simp] theorem isoOfFourGenerators_app (h : FourGeneratorLaws X M N Y p) (z : farLeft X M N Y) :
    (isoOfFourGenerators X M N Y p h).hom.app z = (p z).hom := rfl

/-- The four families of tests characterize naturality on every quotient arrow, including inverse balances. -/
theorem fourGeneratorLaws_iff :
    FourGeneratorLaws X M N Y p ↔ ∀ {x y : farLeft X M N Y} (f : x ⟶ y), CompareAt p f := by
  constructor
  · intro h x y f
    exact (isoOfFourGenerators X M N Y p h).hom.naturality f
  · intro h
    constructor <;> intros <;> exact h _

/-- Object equalities and the four transported generator tests give equality of the entire functors. -/
theorem extFourGenerators (q : ∀ z, H.obj z = K.obj z) (h : FourGeneratorLaws X M N Y (fun z => eqToIso (q z))) : H = K :=
  Functor.ext_of_iso (isoOfFourGenerators X M N Y (fun z => eqToIso (q z)) h) q (fun _ => rfl)

end Four

end ContextualComposition.RelativeTensor.Iterated
