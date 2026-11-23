module
public import ContextualComposition.NativeFubiniTree
@[expose] public section

/-! The actual arbitrary-tree comparison has the recursively addressed
coefficient shuffle, not just the recursive carrier map. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

namespace OrderedDependentAugData

set_option backward.isDefEq.respectTransparency false in
theorem dependentUnitFubini_hom_trace [i : IsIso (J.ρ I)] :
    let F : RawSingletonFrame PUnit.{u+1} (terminalShape I) :=
      rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
    RawSingletonTrace F (nullaryFrame R L J) (fun _ => inv (J.ρ I))
      (dependentUnitFubini R L hl hr J).hom.native := by
  intro F
  let A := (OrderedDependentAugData.unit I).accumulate R L J
  let e := dependentUnitFubini R L hl hr J
  let f : Fin 1 ≃ Fin A.base.n := Equiv.refl (Fin 1)
  let a := fun _ : Fin A.base.n => inv (J.ρ I)
  let b := fun _ : Fin 1 => J.ρ I
  let q : Hom ℙ (terminalShape I) A.base := nativeSingletonMap f a
  have h : e.inv.native = nativeSingletonMap (A:=A.base) (B:=terminalShape I) f.symm b := by
    obtain ⟨g,p,he,_,hp⟩ := dependentUnitFubini_inv_trace R L J hl hr
    have G : g = f.symm := by
      apply Equiv.ext
      intro j
      change (_ : Fin 1) = (_ : Fin 1)
      exact Subsingleton.elim _ _
    subst g
    rw [he]
    congr 1
    funext j
    exact eq_of_heq (hp j)
  have k : q.comp e.inv.native = Hom.ident (terminalShape I) := by
    rw [h]
    change (nativeSingletonMap (A:=terminalShape I) (B:=A.base) f a).comp (nativeSingletonMap (A:=A.base) (B:=terminalShape I) f.symm b) = _
    rw [nativeSingletonMap_comp]
    have eq : f.trans f.symm = Equiv.refl (Fin 1) := Equiv.ext fun _ => rfl
    rw [nativeSingletonMap_ident (terminalShape I) |>.symm]
    have x : (fun j : Fin 1 => a (f j) ≫ b j) = (fun _ => 𝟙 I) := by
      funext j
      exact IsIso.inv_hom_id (J.ρ I)
    change nativeSingletonMap (A:=terminalShape I) (B:=terminalShape I) (Equiv.refl (Fin 1)) (fun j : Fin 1 => a (f j) ≫ b j) = _
    rw [x]
    rfl
  have ei := congrArg AugHom.native e.inv_hom
  change e.inv.native.comp e.hom.native = Hom.ident A.base at ei
  have qe : q = e.hom.native := by
    calc
      q = q.comp (Hom.ident A.base) := (Hom.comp_ident _).symm
      _ = (q.comp e.inv.native).comp e.hom.native := by rw [← ei, Hom.comp_assoc]
      _ = e.hom.native := by rw [k, Hom.ident_comp]
  exact ⟨f,a,qe.symm,fun _ => Subsingleton.elim _ _,fun _ => HEq.rfl⟩
end OrderedDependentAugData

namespace DependentFubiniTree
open OrderedDependentAugData

/-- Nested raw address pairs, with one syntactic address at a unit vertex.
Equal interpreted coefficient labels do not identify addresses. -/
def Address : DependentFubiniTree I → Type u
  | .unit => PUnit.{u+1}
  | .leaf A => A.Branch
  | .fork a b => Address a × Address b

def branchRead : (a : DependentFubiniTree I) → (a.jointInput R L J).Branch ≃ a.Address
  | .unit =>
    ⟨fun _ => PUnit.unit, fun _ => (PUnit.unit,PUnit.unit), fun x => nullaryBranch_eq _ x, fun _ => rfl⟩
  | .leaf A => Equiv.refl A.Branch
  | .fork a b => (jointRead (a.jointInput R L J) (b.jointInput R L J)).trans
      (Equiv.prodCongr (branchRead a) (branchRead b))

def parentCoeff : (a : DependentFubiniTree I) → a.Address → C
  | .unit, _ => I
  | .leaf A, x => A.V x.1
  | .fork a b, x => T.obj (parentCoeff a x.1) (parentCoeff b x.2)

def childCoeff : (a : DependentFubiniTree I) → a.Address → C
  | .unit, _ => I
  | .leaf A, x => A.A x.1 x.2
  | .fork a b, x => T.obj (childCoeff a x.1) (childCoeff b x.2)

def separateCoeff : (a : DependentFubiniTree I) → a.Address → C
  | .unit, _ => I
  | .leaf A, x => T.obj (A.V x.1) (A.A x.1 x.2)
  | .fork a b, x => T.obj (separateCoeff a x.1) (separateCoeff b x.2)

abbrev jointCoeff (a : DependentFubiniTree I) (x : a.Address) :=
  T.obj (parentCoeff (T:=T) a x) (childCoeff (T:=T) a x)

omit lF rF in
theorem parentCoeff_read : (a : DependentFubiniTree I) → (x : (a.jointInput R L J).Branch) →
    (a.jointInput R L J).V x.1 = parentCoeff (T:=T) a (branchRead R L J a x)
  | .unit, _ => rfl
  | .leaf _, _ => rfl
  | .fork a b, x => congrArg₂ T.obj (parentCoeff_read a (x.1.1,x.2.1)) (parentCoeff_read b (x.1.2,x.2.2))

omit lF rF in
theorem childCoeff_read : (a : DependentFubiniTree I) → (x : (a.jointInput R L J).Branch) →
    (a.jointInput R L J).A x.1 x.2 = childCoeff (T:=T) a (branchRead R L J a x)
  | .unit, _ => rfl
  | .leaf _, _ => rfl
  | .fork a b, x => congrArg₂ T.obj (childCoeff_read a (x.1.1,x.2.1)) (childCoeff_read b (x.1.2,x.2.2))

noncomputable def separateFrame : (a : DependentFubiniTree I) → RawSingletonFrame a.Address (a.separate R L J).base
  | .unit => rawWordFrame (fun _ : PUnit.{u+1} => I) [PUnit.unit] (by simp)
  | .leaf A => A.accFrame R L J
  | .fork a b => (separateFrame a).tensor T (separateFrame b)

omit lF rF in
theorem separateFrame_coeff : (a : DependentFubiniTree I) → (x : a.Address) →
    (separateFrame R L J a).label x = separateCoeff (T:=T) a x
  | .unit, _ => rfl
  | .leaf _, _ => rfl
  | .fork a b, x => congrArg₂ T.obj (separateFrame_coeff a x.1) (separateFrame_coeff b x.2)

noncomputable def separateTagFrame (a : DependentFubiniTree I) :
    RawSingletonFrame a.Address (a.separate R L J).base :=
  (separateFrame R L J a).relabel id Function.injective_id (separateCoeff (T:=T) a) (separateFrame_coeff R L J a)

noncomputable def jointTagFrame (a : DependentFubiniTree I) :
    RawSingletonFrame a.Address ((a.jointInput R L J).accumulate R L J).base :=
  let e := branchRead R L J a
  ((a.jointInput R L J).accFrame R L J).relabel e e.injective (jointCoeff (T:=T) a)
    (fun x => congrArg₂ T.obj (parentCoeff_read R L J a x) (childCoeff_read R L J a x))

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [iρ : IsIso (J.ρ I)]

/-- The coefficient law is computed separately from the native comparison. -/
def coefficient (unitCell : I ⟶ T.obj I I) : (a : DependentFubiniTree I) → (x : a.Address) →
    separateCoeff (T:=T) a x ⟶ jointCoeff (T:=T) a x
  | .unit, _ => unitCell
  | .leaf _, _ => 𝟙 _
  | .fork a b, x =>
    T.map (coefficient unitCell a x.1) (coefficient unitCell b x.2) ≫
      m.cell (parentCoeff a x.1) (childCoeff a x.1) (parentCoeff b x.2) (childCoeff b x.2)

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem medial_cell_heq {a b c d a' b' c' d' : C}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    HEq (m.cell a b c d) (m.cell a' b' c' d') := by
  subst a'; subst b'; subst c'; subst d'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3400000 in
theorem comparison_trace (a : DependentFubiniTree I) :
    RawSingletonTrace (a.separateTagFrame R L J) (a.jointTagFrame R L J) (coefficient (m:=m) (inv (J.ρ I)) a)
      (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom.native := by
  induction a with
  | unit =>
    have h := dependentUnitFubini_hom_trace R L J hl hr
    exact h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  | leaf A =>
    exact (RawSingletonTrace.ident (A.accFrame R L J)).changeFrame
      (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  | fork a b ha hb =>
    let d := a.jointInput R L J
    let e := b.jointInput R L J
    let r := Equiv.prodCongr (a.branchRead R L J) (b.branchRead R L J)
    let F := (a.separateTagFrame R L J).tensor T (b.separateTagFrame R L J)
    let G := (a.jointTagFrame R L J).tensor T (b.jointTagFrame R L J)
    let H := (DependentFubiniTree.fork a b).jointTagFrame R L J
    let X (z : a.Address × b.Address) := T.obj (jointCoeff (T:=T) a z.1) (jointCoeff (T:=T) b z.2)
    let Y (z : a.Address × b.Address) := jointCoeff (T:=T) (.fork a b) z
    let sh (z : a.Address × b.Address) : X z ⟶ Y z :=
      m.cell (parentCoeff a z.1) (childCoeff a z.1) (parentCoeff b z.2) (childCoeff b z.2)
    let φ := d.binaryFubini R L J N NR NL hl hr m mi h j unit_middle e
    have T₁ : RawSingletonTrace F G
        (fun z => T.map (coefficient (m:=m) (inv (J.ρ I)) a z.1) (coefficient (m:=m) (inv (J.ρ I)) b z.2))
        (independentNativeWordMap T (a.comparison R L J N NR NL hl hr m mi h j unit_middle).hom.native
          (b.comparison R L J N NR NL hl hr m mi h j unit_middle).hom.native R L) :=
      ha.tensor R L hl hr hb
    have T₂ : RawSingletonTrace G H sh φ.hom.native := by
      have p (z : d.Branch × e.Branch) : ((d.accFrame R L J).tensor T (e.accFrame R L J)).label z = X (r z) :=
        congrArg₂ T.obj
          (congrArg₂ T.obj (parentCoeff_read R L J a z.1) (childCoeff_read R L J a z.1))
          (congrArg₂ T.obj (parentCoeff_read R L J b z.2) (childCoeff_read R L J b z.2))
      have q (z : d.Branch × e.Branch) : (d.jointFrame R L J e).label z = Y (r z) :=
        congrArg₂ T.obj
          (congrArg₂ T.obj (parentCoeff_read R L J a z.1) (parentCoeff_read R L J b z.2))
          (congrArg₂ T.obj (childCoeff_read R L J a z.1) (childCoeff_read R L J b z.2))
      have t := (binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr d e).relabel r r.injective
        X Y p q sh (fun z => medial_cell_heq m (parentCoeff_read R L J a z.1) (childCoeff_read R L J a z.1)
          (parentCoeff_read R L J b z.2) (childCoeff_read R L J b z.2))
      exact t.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
    exact (T₁.comp T₂).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
