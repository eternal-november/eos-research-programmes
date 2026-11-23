module
public import ContextualComposition.NativeAdmissibleFubini
@[expose] public section

/-! Native simultaneous Fubini for admissible input displays and every
native dependent map between them; no chosen words are input data. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {T : Bi (coeff (C:=C))} {I : C}
variable {A : Type u}

/-- An admissible dependent input has the parent display and the
continuation display over its extension. -/
structure AdmissibleDependentInput (K : NativeProjectionClass.{u}) (A : Type u) (I : C) where
  parent : Admissible (C:=C) (I:=I) (A:=A) K
  child : Admissible (C:=C) (I:=I) (A:=parent.obj.Extension) K

/-- No condition that an input arrow itself be a display map. -/
structure AdmissibleDependentArrow {K : NativeProjectionClass.{u}} (P Q : AdmissibleDependentInput K A I) where
  parent : P.parent ⟶ Q.parent
  child : ∀ z : P.parent.obj.Extension, AugHom (standardPush (C:=C))
    (P.child.obj z) (Q.child.obj (extensionMap parent.hom z))

namespace AdmissibleDependentInput
variable {K : NativeProjectionClass.{u}} (P : AdmissibleDependentInput K A I)

noncomputable def ordered : A → OrderedDependentAugData I := nativePresentation P.parent.obj P.child.obj

theorem ordered_admissible : OrderedAdmissible P.ordered K :=
  nativePresentation_admissible K P.parent.obj P.child.obj P.parent.property P.child.property

end AdmissibleDependentInput

namespace AdmissibleDependentArrow
variable {K : NativeProjectionClass.{u}} {P Q : AdmissibleDependentInput K A I}
variable (p : AdmissibleDependentArrow P Q)

set_option backward.isDefEq.respectTransparency false in
noncomputable def ordered (x : A) : OrderedDependentAugArrow (P.ordered x) (Q.ordered x) :=
  NativeDependentPairHom.ordered
    (⟨p.parent.hom x,fun i => p.child ⟨x,⟨i⟩⟩⟩ :
      NativeDependentPairHom (P.parent.obj.pairAt P.child.obj x) (Q.parent.obj.pairAt Q.child.obj x))

end AdmissibleDependentArrow

variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (K : NativeProjectionClass.{u})

noncomputable def nativeFubiniSeparate
    (n : Nat) (P : Fin n → AdmissibleDependentInput K A I) : Admissible (C:=C) (I:=I) (A:=A) K :=
  fubiniSeparateDisplay R L J K n (fun i => (P i).ordered) (fun i => (P i).ordered_admissible)

noncomputable def nativeFubiniJoint
    (n : Nat) (P : Fin n → AdmissibleDependentInput K A I) : Admissible (C:=C) (I:=I) (A:=A) K :=
  fubiniJointDisplay R L J K n (fun i => (P i).ordered) (fun i => (P i).ordered_admissible)

variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]

noncomputable def nativeAdmissibleFubini
    (n : Nat) (P : Fin n → AdmissibleDependentInput K A I) :
    nativeFubiniSeparate R L J K n P ≅ nativeFubiniJoint R L J K n P :=
  admissibleFubini R L J K N NR NL hl hr m mi h j unit_middle n (fun i => (P i).ordered)
    (fun i => (P i).ordered_admissible)

set_option backward.isDefEq.respectTransparency false in
noncomputable def nativeFubiniSeparateMap (n : Nat) {P Q : Fin n → AdmissibleDependentInput K A I}
    (p : ∀ i, AdmissibleDependentArrow (P i) (Q i)) :
    nativeFubiniSeparate R L J K n P ⟶ nativeFubiniSeparate R L J K n Q :=
  ObjectProperty.homMk (fubiniSeparateMap R L J N NR NL hl hr n (fun i => (p i).ordered))

set_option backward.isDefEq.respectTransparency false in
noncomputable def nativeFubiniJointMap (n : Nat) {P Q : Fin n → AdmissibleDependentInput K A I}
    (p : ∀ i, AdmissibleDependentArrow (P i) (Q i)) :
    nativeFubiniJoint R L J K n P ⟶ nativeFubiniJoint R L J K n Q :=
  ObjectProperty.homMk (fubiniJointMap R L J N NR NL hl hr n (fun i => (p i).ordered))

set_option backward.isDefEq.respectTransparency false in
/-- The actual simultaneous Fubini square, on all aggregated native
arrows between objects with admissible parent and continuation displays. -/
theorem nativeAdmissibleFubini_natural (n : Nat) {P Q : Fin n → AdmissibleDependentInput K A I}
    (p : ∀ i, AdmissibleDependentArrow (P i) (Q i)) :
    nativeFubiniSeparateMap R L J K N NR NL hl hr n p ≫
      (nativeAdmissibleFubini R L J K N NR NL hl hr m mi h j unit_middle n Q).hom =
    (nativeAdmissibleFubini R L J K N NR NL hl hr m mi h j unit_middle n P).hom ≫
      nativeFubiniJointMap R L J K N NR NL hl hr n p :=
  admissibleFubini_natural R L J K N NR NL hl hr m mi h j unit_middle n
    (fun i => (P i).ordered_admissible) (fun i => (Q i).ordered_admissible) (fun i => (p i).ordered)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
