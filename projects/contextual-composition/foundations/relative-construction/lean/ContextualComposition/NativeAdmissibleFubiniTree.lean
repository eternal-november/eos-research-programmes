module
public import ContextualComposition.NativeAdmissibleFiniteFubini
public import ContextualComposition.NativeFubiniTreeStructuralPath
@[expose] public section

/-! Arbitrary-shape indexed Fubini in the literal admissible full
subcategory. The base can be empty and need not be finite. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {A : Type u} {I : C} {K : NativeProjectionClass.{u}}
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)

inductive AdmissibleFubiniTree (K : NativeProjectionClass.{u}) (A : Type u) (I : C)
    : Type (max (u+1) v) where
  | unit
  | leaf (D : AdmissibleDependentInput K A I)
  | fork (l r : AdmissibleFubiniTree K A I)

namespace AdmissibleFubiniTree

noncomputable def eval : AdmissibleFubiniTree K A I → A → DependentFubiniTree I
  | .unit, _ => .unit
  | .leaf D, x => .leaf (D.ordered x)
  | .fork l r, x => .fork (eval l x) (eval r x)

set_option backward.isDefEq.respectTransparency false in
theorem admissible_jointInput : (a : AdmissibleFubiniTree K A I) →
    OrderedAdmissible (fun x => (a.eval x).jointInput R L J) K
  | .unit => orderedUnit_admissible K
  | .leaf D => D.ordered_admissible
  | .fork l r => orderedProduct_admissible R L J (fun x => (l.eval x).jointInput R L J)
      (fun x => (r.eval x).jointInput R L J) K (admissible_jointInput l) (admissible_jointInput r)

set_option backward.isDefEq.respectTransparency false in
theorem admissible_separate : (a : AdmissibleFubiniTree K A I) →
    admissible K (fun x => (a.eval x).separate R L J)
  | .unit => unit_admissible K
  | .leaf D => orderedAcc_admissible R L J D.ordered K D.ordered_admissible
  | .fork l r => tensor_admissible K R L J (fun x => (l.eval x).separate R L J)
      (fun x => (r.eval x).separate R L J) (admissible_separate l) (admissible_separate r)

noncomputable def separateDisplay (a : AdmissibleFubiniTree K A I) :
    Admissible (C:=C) (A:=A) (I:=I) K :=
  ⟨fun x => (a.eval x).separate R L J, a.admissible_separate R L J⟩

noncomputable def jointDisplay (a : AdmissibleFubiniTree K A I) :
    Admissible (C:=C) (A:=A) (I:=I) K :=
  ⟨orderedAcc R L J (fun x => (a.eval x).jointInput R L J),
    orderedAcc_admissible R L J _ K (a.admissible_jointInput R L J)⟩

variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

/-- Pointwise read of one structural step on indexed displayed inputs. -/
inductive Move : AdmissibleFubiniTree K A I → AdmissibleFubiniTree K A I → Type (max (u+1) v) where
  | assoc (a b c : AdmissibleFubiniTree K A I) : Move (.fork (.fork a b) c) (.fork a (.fork b c))
  | swap (a b : AdmissibleFubiniTree K A I) : Move (.fork a b) (.fork b a)
  | eraseRight (a : AdmissibleFubiniTree K A I) : Move (.fork a .unit) a
  | left {a b : AdmissibleFubiniTree K A I} (p : Move a b) (c : AdmissibleFubiniTree K A I) :
      Move (.fork a c) (.fork b c)
  | right (c : AdmissibleFubiniTree K A I) {a b : AdmissibleFubiniTree K A I} (p : Move a b) :
      Move (.fork c a) (.fork c b)

noncomputable def Move.eval {a b : AdmissibleFubiniTree K A I} (p : Move a b) (x : A) :
    DependentFubiniTree.StructuralMove (a.eval x) (b.eval x) :=
  match p with
  | .assoc a b c => .assoc (.root (a.eval x) (b.eval x) (c.eval x))
  | .swap a b => .swap (a.eval x) (b.eval x)
  | .eraseRight a => .eraseRight (a.eval x)
  | .left p c => .left (p.eval x) (c.eval x)
  | .right c p => .right (c.eval x) (p.eval x)

inductive Path : AdmissibleFubiniTree K A I → AdmissibleFubiniTree K A I → Type (max (u+1) v) where
  | ident (a : AdmissibleFubiniTree K A I) : Path a a
  | next {a b c : AdmissibleFubiniTree K A I} (p : Move a b) (q : Path b c) : Path a c
  | prev {a b c : AdmissibleFubiniTree K A I} (p : Move b a) (q : Path b c) : Path a c

noncomputable def Path.eval {a b : AdmissibleFubiniTree K A I} (p : Path a b) (x : A) :
    DependentFubiniTree.StructuralPath (a.eval x) (b.eval x) :=
  match p with
  | .ident a => .ident (a.eval x)
  | .next p q => .next (p.eval x) (q.eval x)
  | .prev p q => .prev (p.eval x) (q.eval x)

/-- Same-shape tree map with all actual parent and continuation arrows at a leaf. -/
inductive Map : AdmissibleFubiniTree K A I → AdmissibleFubiniTree K A I → Type (max (u+1) v) where
  | unit : Map .unit .unit
  | leaf {P Q : AdmissibleDependentInput K A I} (p : AdmissibleDependentArrow P Q) : Map (.leaf P) (.leaf Q)
  | fork {a b c d : AdmissibleFubiniTree K A I} (p : Map a b) (q : Map c d) : Map (.fork a c) (.fork b d)

noncomputable def Map.eval {a b : AdmissibleFubiniTree K A I} (p : Map a b) (x : A) :
    DependentFubiniTree.Map (a.eval x) (b.eval x) :=
  match p with
  | .unit => .unit
  | .leaf p => .leaf (p.ordered x)
  | .fork p q => .fork (p.eval x) (q.eval x)

set_option backward.isDefEq.respectTransparency false in
noncomputable def Map.separate {a b : AdmissibleFubiniTree K A I} (p : Map a b) :
    a.separateDisplay R L J ⟶ b.separateDisplay R L J :=
  ObjectProperty.homMk (fun x => (p.eval x).separate R L J N NR NL hl hr)

set_option backward.isDefEq.respectTransparency false in
noncomputable def Map.joint {a b : AdmissibleFubiniTree K A I} (p : Map a b) :
    a.jointDisplay R L J ⟶ b.jointDisplay R L J :=
  ObjectProperty.homMk (fun x => ((p.eval x).joint R L J N NR NL hl hr).accumulate R L J N NL hl)

section Path
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable (ia : ∀ a b c, IsIso (P.assoc a b c))
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (is : ∀ a b, IsIso (P.swap a b))
variable (iu : ∀ a, IsIso (J.ρ a))
variable {a b : AdmissibleFubiniTree K A I}
variable (p : ∀ x : A, DependentFubiniTree.StructuralPath (a.eval x) (b.eval x))

set_option backward.isDefEq.respectTransparency false in
noncomputable def pathSeparateIso :
    a.separateDisplay R L J ≅ b.separateDisplay R L J :=
  let e x := (p x).separateIso R L J N NR NL hl hr P Q U ia swap_unit is iu
  ObjectProperty.isoMk (admissible (C:=C) (A:=A) (I:=I) K)
    { hom := fun x => (e x).hom
      inv := fun x => (e x).inv
      hom_inv_id := funext fun x => (e x).hom_inv
      inv_hom_id := funext fun x => (e x).inv_hom }

set_option backward.isDefEq.respectTransparency false in
noncomputable def pathJointIso :
    a.jointDisplay R L J ≅ b.jointDisplay R L J :=
  let e x := (p x).jointIso R L J N NR NL hl hr P Q U ia swap_unit is iu
  ObjectProperty.isoMk (admissible (C:=C) (A:=A) (I:=I) K)
    { hom := fun x => (e x).hom
      inv := fun x => (e x).inv
      hom_inv_id := funext fun x => (e x).hom_inv
      inv_hom_id := funext fun x => (e x).inv_hom }

end Path

section Comparison
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]

set_option backward.isDefEq.respectTransparency false in
noncomputable def comparison (a : AdmissibleFubiniTree K A I) :
    a.separateDisplay R L J ≅ a.jointDisplay R L J :=
  ObjectProperty.isoMk (admissible (C:=C) (A:=A) (I:=I) K)
    { hom := fun x => ((a.eval x).comparison R L J N NR NL hl hr m mi h j unit_middle).hom
      inv := fun x => ((a.eval x).comparison R L J N NR NL hl hr m mi h j unit_middle).inv
      hom_inv_id := funext fun x => ((a.eval x).comparison R L J N NR NL hl hr m mi h j unit_middle).hom_inv
      inv_hom_id := funext fun x => ((a.eval x).comparison R L J N NR NL hl hr m mi h j unit_middle).inv_hom }

set_option backward.isDefEq.respectTransparency false in
theorem Map.comparison_natural {a b : AdmissibleFubiniTree K A I} (p : Map a b) :
    p.separate R L J N NR NL hl hr ≫ (b.comparison R L J N NR NL hl hr m mi h j unit_middle).hom =
    (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom ≫ p.joint R L J N NR NL hl hr := by
  apply ObjectProperty.hom_ext
  funext x
  exact DependentFubiniTree.comparison_natural R L J N NR NL hl hr m mi h j unit_middle (p.eval x)

variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable (ia : ∀ a b c, IsIso (P.assoc a b c))
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I)
variable (is : ∀ a b, IsIso (P.swap a b))
variable (iu : ∀ a, IsIso (J.ρ a))

set_option backward.isDefEq.respectTransparency false in
omit [IsIso (J.ρ I)] in
theorem path_fubini {a b : AdmissibleFubiniTree K A I}
    (p : ∀ x : A, DependentFubiniTree.StructuralPath (a.eval x) (b.eval x))
    (law : FubiniTreeLaws R J P m) :
    (pathSeparateIso R L J N NR NL hl hr P Q U ia swap_unit is iu p).hom ≫
      (b.comparison R L J N NR NL hl hr m mi h j unit_middle).hom =
    (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom ≫
      (pathJointIso R L J N NR NL hl hr P Q U ia swap_unit is iu p).hom := by
  apply ObjectProperty.hom_ext
  funext x
  exact (p x).fubini R L J N NR NL hl hr P Q U ia swap_unit is iu m mi h j unit_middle law

end Comparison
end AdmissibleFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.IndexedNativeFamily
