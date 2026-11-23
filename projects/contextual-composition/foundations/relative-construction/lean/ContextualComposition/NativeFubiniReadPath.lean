module
public import ContextualComposition.NativeFubiniTreeAssocMove
@[expose] public section

/-! Product whiskering of sequences of actual dependent reads, without
choosing a new scalar chart for the whole composite. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {I : C} {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
local notation "prd" => OrderedDependentAugData.product R L J
local notation "acc" => OrderedDependentAugData.accumulate R L J
local notation "ind" => independentAug R L (J.ρ I)
local notation "nm" => independentAugMap R L (J.ρ I) N NR NL hl hr
local notation "rc" => OrderedDependentAugData.ReadComparison.accumulate R L J NL hl
local notation "rid" => OrderedDependentAugData.identityRead

inductive OrderedReadPath : OrderedDependentAugData I → OrderedDependentAugData I → Type (max (u+1) v) where
  | nil (A : OrderedDependentAugData I) : OrderedReadPath A A
  | cons {A B D : OrderedDependentAugData I} (p : A.ReadComparison B) (q : OrderedReadPath B D) :
      OrderedReadPath A D

namespace OrderedReadPath

noncomputable def iso {A B : OrderedDependentAugData I} (p : OrderedReadPath A B) :
    NativeAugmentedIso (acc A) (acc B) :=
  match p with
  | .nil _ => NativeAugmentedIso.ident _
  | .cons p q => (rc p).trans (q.iso)

def append {A B D : OrderedDependentAugData I} (p : OrderedReadPath A B) (q : OrderedReadPath B D) :
    OrderedReadPath A D :=
  match p with
  | .nil _ => q
  | .cons p p' => .cons p (p'.append q)

omit rF in
theorem append_hom {A B D : OrderedDependentAugData I} (p : OrderedReadPath A B) (q : OrderedReadPath B D) :
    ((p.append q).iso R L J NL hl).hom = ((p.iso R L J NL hl).hom).comp (q.iso R L J NL hl).hom := by
  induction p with
  | nil _ => exact (AugHom.ident_comp _).symm
  | cons p p' ih =>
    change (rc p).hom.comp ((p'.append q).iso R L J NL hl).hom =
      ((rc p).hom.comp (p'.iso R L J NL hl).hom).comp (q.iso R L J NL hl).hom
    rw [ih, AugHom.comp_assoc]

noncomputable def left {A B : OrderedDependentAugData I} (p : OrderedReadPath A B)
    (D : OrderedDependentAugData I) : OrderedReadPath (prd A D) (prd B D) :=
  match p with
  | .nil A => .nil (prd A D)
  | .cons p q => .cons (p.product R L J NR NL hl hr (rid D)) (q.left D)

noncomputable def right (A : OrderedDependentAugData I) {B D : OrderedDependentAugData I}
    (p : OrderedReadPath B D) : OrderedReadPath (prd A B) (prd A D) :=
  match p with
  | .nil B => .nil (prd A B)
  | .cons p q => .cons ((rid A).product R L J NR NL hl hr p) (right A q)

noncomputable def product {A B D E : OrderedDependentAugData I} (p : OrderedReadPath A B)
    (q : OrderedReadPath D E) : OrderedReadPath (prd A D) (prd B E) :=
  (p.left R L J NR NL hl hr D).append (right R L J NR NL hl hr B q)

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
local notation "ph" => OrderedDependentAugData.binaryFubini R L J N NR NL hl hr m mi h j unit_middle
local notation "ri" => iso R L J NL hl

set_option backward.isDefEq.respectTransparency false in
theorem left_fubini {A B : OrderedDependentAugData I} (p : OrderedReadPath A B)
    (D : OrderedDependentAugData I) :
    (nm (ri p).hom (AugHom.ident (acc D))).comp (ph B D).hom =
      (ph A D).hom.comp (ri (p.left R L J NR NL hl hr D)).hom := by
  induction p with
  | nil A => simp only [iso, left, NativeAugmentedIso.ident, independentAugMap_ident,
      AugHom.ident_comp, AugHom.comp_ident]
  | @cons A B E a p ih =>
    have t := OrderedDependentAugData.ReadComparison.binaryFubini_natural R L J N NR NL hl hr
      m mi h j unit_middle a (rid D)
    rw [OrderedDependentAugData.identityRead_accumulate] at t
    change (nm ((rc a).hom.comp (ri p).hom) (AugHom.ident (acc D))).comp (ph E D).hom =
      (ph A D).hom.comp ((rc (a.product R L J NR NL hl hr (rid D))).hom.comp
        (ri (p.left R L J NR NL hl hr D)).hom)
    rw [← AugHom.ident_comp (AugHom.ident (acc D)), independentAugMap_comp, AugHom.comp_assoc,
      ih, ← AugHom.comp_assoc, t, AugHom.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem right_fubini (A : OrderedDependentAugData I) {B D : OrderedDependentAugData I}
    (p : OrderedReadPath B D) :
    (nm (AugHom.ident (acc A)) (ri p).hom).comp (ph A D).hom =
      (ph A B).hom.comp (ri (right R L J NR NL hl hr A p)).hom := by
  induction p with
  | nil B => simp only [iso, right, NativeAugmentedIso.ident, independentAugMap_ident,
      AugHom.ident_comp, AugHom.comp_ident]
  | @cons B D E a p ih =>
    have t := OrderedDependentAugData.ReadComparison.binaryFubini_natural R L J N NR NL hl hr
      m mi h j unit_middle (rid A) a
    rw [OrderedDependentAugData.identityRead_accumulate] at t
    change (nm (AugHom.ident (acc A)) ((rc a).hom.comp (ri p).hom)).comp (ph A E).hom =
      (ph A B).hom.comp ((rc ((rid A).product R L J NR NL hl hr a)).hom.comp
        (ri (right R L J NR NL hl hr A p)).hom)
    rw [← AugHom.ident_comp (AugHom.ident (acc A)), independentAugMap_comp, AugHom.comp_assoc,
      ih, ← AugHom.comp_assoc, t, AugHom.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem product_fubini {A B D E : OrderedDependentAugData I} (p : OrderedReadPath A B)
    (q : OrderedReadPath D E) :
    (nm (ri p).hom (ri q).hom).comp (ph B E).hom =
      (ph A D).hom.comp (ri (p.product R L J NR NL hl hr q)).hom := by
  have lh := p.left_fubini R L J N NR NL hl hr m mi h j unit_middle D
  have rh := right_fubini R L J N NR NL hl hr m mi h j unit_middle B q
  have split : nm (ri p).hom (ri q).hom =
      (nm (ri p).hom (AugHom.ident (acc D))).comp (nm (AugHom.ident (acc B)) (ri q).hom) := by
    rw [← independentAugMap_comp, AugHom.comp_ident, AugHom.ident_comp]
  unfold product
  rw [append_hom, split, AugHom.comp_assoc, rh, ← AugHom.comp_assoc, lh, AugHom.comp_assoc]

end OrderedReadPath
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
