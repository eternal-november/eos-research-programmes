module
public import ContextualComposition.RelativeTensorFourGeneratorComparison
public import ContextualComposition.RelativeTensorUnitModule

@[expose] public section
namespace ContextualComposition.RelativeTensor.Iterated.UnitTriangle

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false

universe v u vX uX vY uY
variable {B : Type u} [Category.{v} B]
variable (X : LocallyDiscrete B ⥤ᵖ Cat.{vX,uX}) (Y : LocallyDiscrete Bᵒᵖ ⥤ᵖ Cat.{vY,uY})

/-- A native pair commutes with the actual balancing isomorphism at the middle hom label. -/
theorem native_square {i j : B} (p : i ⟶ j) {x x' : X.obj ⟨i⟩} {y y' : Y.obj ⟨op j⟩}
    (f : x ⟶ x') (g : y ⟶ y') :
    (insertion X Y i).map (productMap f ((backward Y p).map g)) ≫ (balancing X Y p x' y').hom =
      (balancing X Y p x y).hom ≫ (insertion X Y j).map (productMap ((forward X p).map f) g) :=
  (restrict (𝟭 (Tensor X Y))).natural p f g

private theorem cancelLast {T : Type*} [Category* T] {a b c d e : T}
    (l : a ≅ b) (f : b ⟶ c) (g : c ⟶ d) (r : e ≅ d) (w : a ⟶ e)
    (h : w = l.hom ≫ f ≫ g ≫ r.inv) : (l.hom ≫ f) ≫ g = w ≫ r.hom := by
  rw [h]
  simp

private theorem cancelFirst {T : Type*} [Category* T] {a b c d e : T}
    (l : a ≅ b) (f : b ⟶ c) (g : c ⟶ d) (r : e ≅ d) (w : a ⟶ e)
    (h : w = l.hom ≫ f ≫ g ≫ r.inv) : l.inv ≫ w = (f ≫ g) ≫ r.inv := by
  rw [h]
  simp

private abbrev contravCorrection {i j k : B} (u : i ⟶ j) (v : j ⟶ k)
    (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :=
  (insertion X Y i).mapIso ((Iso.refl x).prod ((Cat.Hom.toNatIso (Y.mapComp v.op.toLoc u.op.toLoc)).app y))

private abbrev covCorrection {i j k : B} (u : i ⟶ j) (v : j ⟶ k)
    (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :=
  (insertion X Y k).mapIso (((Cat.Hom.toNatIso (X.mapComp u.toLoc v.toLoc)).app x).prod (Iso.refl y))

/-- Naturality at the inner junction. The covariant compositor is cancelled on the right
of the balance composition relation. -/
theorem inner_square {i j k : B} (u : i ⟶ j) (p : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    ((insertion X Y i).map (productMap (𝟙 x) ((Y.mapComp p.op.toLoc u.op.toLoc).hom.toNatTrans.app y)) ≫
      (balancing X Y u x ((backward Y p).obj y)).hom) ≫ (balancing X Y p ((forward X u).obj x) y).hom =
      (balancing X Y (u ≫ p) x y).hom ≫
        (insertion X Y k).map (productMap ((X.mapComp u.toLoc p.toLoc).hom.toNatTrans.app x) (𝟙 y)) :=
  cancelLast (contravCorrection X Y u p x y) (balancing X Y u x ((backward Y p).obj y)).hom
    (balancing X Y p ((forward X u).obj x) y).hom (covCorrection X Y u p x y)
    (balancing X Y (u ≫ p) x y).hom ((restrict (𝟭 (Tensor X Y))).comp u p x y)

/-- Naturality at the outer junction. The contravariant compositor is cancelled on the left
of the same balance composition relation. -/
theorem outer_square {i j k : B} (p : i ⟶ j) (v : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    (insertion X Y i).map (productMap (𝟙 x) ((Y.mapComp v.op.toLoc p.op.toLoc).inv.toNatTrans.app y)) ≫
      (balancing X Y (p ≫ v) x y).hom =
        ((balancing X Y p x ((backward Y v).obj y)).hom ≫
          (balancing X Y v ((forward X p).obj x) y).hom) ≫
            (insertion X Y k).map (productMap ((X.mapComp p.toLoc v.toLoc).inv.toNatTrans.app x) (𝟙 y)) :=
  cancelFirst (contravCorrection X Y p v x y) (balancing X Y p x ((backward Y v).obj y)).hom
    (balancing X Y v ((forward X p).obj x) y).hom (covCorrection X Y p v x y)
    (balancing X Y (p ≫ v) x y).hom ((restrict (𝟭 (Tensor X Y))).comp p v x y)

section Assembly
variable {T : Type*} [Category* T] {H K : Left X (unitModule B) Y ⥤ T}
variable (t : ∀ z, H.obj z ≅ K.obj z)

/-- All three tests are on vertices and arrows of the actual ternary quotient with a discrete
hom as its middle factor. Native middle arrows reduce to equality of their labels. -/
structure GeneratorLaws : Prop where
  native {i j : B} (p : i ⟶ j) {x x' : X.obj ⟨i⟩} {y y' : Y.obj ⟨op j⟩} (f : x ⟶ x') (g : y ⟶ y') :
    CompareAt t ((Reverse.insertL X (unitModule B) Y j).map
      (productMap ((insertion X (RightUnit.represented j) i).map (productMap f (𝟙 (Discrete.mk p)))) g))
  inner {i j k : B} (u : i ⟶ j) (p : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    CompareAt t ((Reverse.insertL X (unitModule B) Y k).map
      (productMap (balancing X (RightUnit.represented k) u x (Discrete.mk p)).hom (𝟙 y)))
  outer {i j k : B} (p : i ⟶ j) (v : j ⟶ k) (x : X.obj ⟨i⟩) (y : Y.obj ⟨op k⟩) :
    CompareAt t (balancing (leftInner X (unitModule B)) Y v
      ((insertion X (RightUnit.represented j) i).obj (x,Discrete.mk p)) y).hom

/-- The three tests give a natural isomorphism on all quotient paths with exactly the proposed
vertex components. -/
def assemble (h : GeneratorLaws X Y t) : H ≅ K := by
  apply isoOfGenerators t
  · intro j z z' y y' q g
    apply tensorParameterComparison (F := X) (G := RightUnit.represented j)
      (Reverse.insertL X (unitModule B) Y j) t ?_ ?_ q g
    · intro i x x' p p' y y' f k g
      obtain rfl : p = p' := Discrete.ext (Discrete.eq_of_hom k)
      have only : k = 𝟙 p := Discrete.hom_eq
      subst k
      exact h.native p.as f g
    · intro i i' u x p y
      exact h.inner u p.as x y
  · intro j k v z y
    obtain ⟨⟨i,x,⟨p⟩⟩⟩ := z
    exact h.outer p v x y

@[simp] theorem assemble_app (h : GeneratorLaws X Y t) (z : Left X (unitModule B) Y) :
    (assemble X Y t h).hom.app z = (t z).hom := rfl

theorem generatorLaws_iff :
    GeneratorLaws X Y t ↔ ∀ {z w : Left X (unitModule B) Y} (f : z ⟶ w), CompareAt t f := by
  constructor
  · intro h z w f; exact (assemble X Y t h).hom.naturality f
  · intro h; constructor <;> intros <;> exact h _

end Assembly
end ContextualComposition.RelativeTensor.Iterated.UnitTriangle
