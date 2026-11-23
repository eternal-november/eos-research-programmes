module
public import ContextualComposition.NativeOrderedContextProduct
@[expose] public section

/-! Pointwise all-length native Fubini in the full subcategory of
admissible context displays. Data and aggregated arrows may vary over
the arbitrary base; the restriction is only on the display objects. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {T : Bi (coeff (C:=C))} {I : C}
variable {A : Type u}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (K : NativeProjectionClass.{u})

section Canonical
variable (P : IndexedNativeFamily (C:=C) A I) (Q : IndexedNativeFamily (C:=C) P.Extension I)
noncomputable def nativePresentation (x : A) : OrderedDependentAugData I := (P.pairAt Q x).ordered

set_option backward.isDefEq.respectTransparency false in
theorem nativePresentation_parent : orderedParent (nativePresentation P Q) = P := by
  funext x
  exact (P.pairAt Q x).parent_recovers

noncomputable def nativePresentation_child_base :
    (orderedParent (nativePresentation P Q)).Extension → P.Extension :=
  fun z => ⟨z.1,⟨((nativePresentation P Q z.1).xs[z.2.down]).down⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem nativePresentation_children :
    orderedChildren (nativePresentation P Q) = Q.reindex (nativePresentation_child_base P Q) := by
  funext z
  exact (P.pairAt Q z.1).child_recovers _

theorem nativePresentation_admissible
    (p : admissible K P) (q : admissible K Q) : OrderedAdmissible (nativePresentation P Q) K := by
  constructor
  · rw [nativePresentation_parent]
    exact p
  · rw [nativePresentation_children]
    exact reindex_admissible K Q q _

end Canonical

def fubiniJointInput (n : Nat) (D : Fin n → A → OrderedDependentAugData I) (x : A) :=
  dependentInputFold R L J n (fun i => D i x)

noncomputable def fubiniSeparate (n : Nat) (D : Fin n → A → OrderedDependentAugData I) :
    IndexedNativeFamily (C:=C) A I :=
  fun x => independentAugFold R L (J.ρ I) n (fun i => (D i x).accumulate R L J)

set_option backward.isDefEq.respectTransparency false in
theorem fubiniJointInput_admissible :
    (n : Nat) → (D : Fin n → A → OrderedDependentAugData I) →
    (∀ i, OrderedAdmissible (D i) K) → OrderedAdmissible (fubiniJointInput R L J n D) K
  | 0, _, _ => orderedUnit_admissible K
  | 1, _, h => h 0
  | n + 2, D, h => orderedProduct_admissible R L J (D 0)
    (fubiniJointInput R L J (n+1) (fun i => D i.succ)) K (h 0)
      (fubiniJointInput_admissible (n+1) (fun i => D i.succ) (fun i => h i.succ))

set_option backward.isDefEq.respectTransparency false in
theorem fubiniSeparate_admissible :
    (n : Nat) → (D : Fin n → A → OrderedDependentAugData I) →
    (∀ i, OrderedAdmissible (D i) K) → admissible K (fubiniSeparate R L J n D)
  | 0, _, _ => unit_admissible K
  | 1, _, h => orderedAcc_admissible R L J _ K (h 0)
  | n + 2, D, h => tensor_admissible K R L J (orderedAcc R L J (D 0))
    (fubiniSeparate R L J (n+1) (fun i => D i.succ)) (orderedAcc_admissible R L J _ K (h 0))
      (fubiniSeparate_admissible (n+1) (fun i => D i.succ) (fun i => h i.succ))

noncomputable def fubiniSeparateDisplay (n : Nat) (D : Fin n → A → OrderedDependentAugData I)
    (h : ∀ i, OrderedAdmissible (D i) K) : Admissible (C:=C) (A:=A) (I:=I) K :=
  ⟨fubiniSeparate R L J n D,fubiniSeparate_admissible R L J K n D h⟩

noncomputable def fubiniJointDisplay (n : Nat) (D : Fin n → A → OrderedDependentAugData I)
    (h : ∀ i, OrderedAdmissible (D i) K) : Admissible (C:=C) (A:=A) (I:=I) K :=
  ⟨orderedAcc R L J (fubiniJointInput R L J n D),
    orderedAcc_admissible R L J _ K (fubiniJointInput_admissible R L J K n D h)⟩

variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]

set_option backward.isDefEq.respectTransparency false in
noncomputable def indexedFubini (n : Nat) (D : Fin n → A → OrderedDependentAugData I) :
    fubiniSeparate R L J n D ≅ orderedAcc R L J (fubiniJointInput R L J n D) where
  hom x := (orderedFubini R L N NR NL hl hr J m mi h j unit_middle n (fun i => D i x)).hom
  inv x := (orderedFubini R L N NR NL hl hr J m mi h j unit_middle n (fun i => D i x)).inv
  hom_inv_id := funext fun x => (orderedFubini R L N NR NL hl hr J m mi h j unit_middle n (fun i => D i x)).hom_inv
  inv_hom_id := funext fun x => (orderedFubini R L N NR NL hl hr J m mi h j unit_middle n (fun i => D i x)).inv_hom

include N NR NL hl hr m mi h j unit_middle in
noncomputable def admissibleFubini (n : Nat) (D : Fin n → A → OrderedDependentAugData I)
    (hd : ∀ i, OrderedAdmissible (D i) K) :
    fubiniSeparateDisplay R L J K n D hd ≅ fubiniJointDisplay R L J K n D hd :=
  ObjectProperty.isoMk (admissible (C:=C) (A:=A) (I:=I) K)
    (X:=fubiniSeparateDisplay R L J K n D hd) (Y:=fubiniJointDisplay R L J K n D hd) (indexedFubini R L J N NR NL hl hr m mi h j unit_middle n D)

set_option backward.isDefEq.respectTransparency false in
noncomputable def fubiniSeparateMap (n : Nat) {D E : Fin n → A → OrderedDependentAugData I}
    (p : ∀ i x, OrderedDependentAugArrow (D i x) (E i x)) :
    fubiniSeparate R L J n D ⟶ fubiniSeparate R L J n E :=
  fun x => independentAugFoldMap R L (J.ρ I) N NR NL hl hr n (fun i => (p i x).accumulate R L J N NL hl)

set_option backward.isDefEq.respectTransparency false in
noncomputable def fubiniJointMap (n : Nat) {D E : Fin n → A → OrderedDependentAugData I}
    (p : ∀ i x, OrderedDependentAugArrow (D i x) (E i x)) :
    orderedAcc R L J (fubiniJointInput R L J n D) ⟶ orderedAcc R L J (fubiniJointInput R L J n E) :=
  fun x => (dependentInputFoldMap R L N NR NL hl hr J n (fun i => p i x)).accumulate R L J N NL hl

set_option backward.isDefEq.respectTransparency false in
theorem admissibleFubini_natural (n : Nat) {D E : Fin n → A → OrderedDependentAugData I}
    (hd : ∀ i, OrderedAdmissible (D i) K) (he : ∀ i, OrderedAdmissible (E i) K)
    (p : ∀ i x, OrderedDependentAugArrow (D i x) (E i x)) :
    ObjectProperty.homMk (X:=fubiniSeparateDisplay R L J K n D hd) (Y:=fubiniSeparateDisplay R L J K n E he)
      (fubiniSeparateMap R L J N NR NL hl hr n p) ≫
      (admissibleFubini R L J K N NR NL hl hr m mi h j unit_middle n E he).hom =
    (admissibleFubini R L J K N NR NL hl hr m mi h j unit_middle n D hd).hom ≫
      ObjectProperty.homMk (X:=fubiniJointDisplay R L J K n D hd) (Y:=fubiniJointDisplay R L J K n E he)
        (fubiniJointMap R L J N NR NL hl hr n p) := by
  apply ObjectProperty.hom_ext (admissible (C:=C) (A:=A) (I:=I) K)
  exact funext fun x => orderedFubini_natural R L N NR NL hl hr J m mi h j unit_middle n (fun i => p i x)

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
