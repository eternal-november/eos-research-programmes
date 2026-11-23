module
public import ContextualComposition.NativeReadComparisonProduct
@[expose] public section

/-! The literal binary Fubini square is natural also for structural
comparisons presented by separately checked ordered parent and child reads. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData
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
variable {A B D E : OrderedDependentAugData I}

def ReadComparison.branchEquiv (p : ReadComparison A B) : A.Branch ≃ B.Branch where
  toFun z := (p.parent.read z.1,(p.child z.1).read z.2)
  invFun z := let u := p.parent.read.symm z.1; (u,(p.child u).read.symm z.2)
  left_inv z := by
    have h := congrArg (fun x => (p.child x).read) (p.parent.read.symm_apply_apply z.1)
    simp only [p.parent.read.symm_apply_apply, h, Equiv.symm_apply_apply]
  right_inv z := by simp

def ReadComparison.coefficient (p : ReadComparison A B) (z : A.Branch) :
    dependentLabels (T:=T) A.V A.A z ⟶ dependentLabels (T:=T) B.V B.A (p.branchEquiv z) :=
  T.map (p.parent.coefficient z.1).hom ((p.child z.1).coefficient z.2).hom

local notation "fr" => accFrame R L J
local notation "acc" => accumulate R L J
local notation "prd" => product R L J
local notation "lift" => ReadComparison.accumulate R L J NL hl
local notation "rd" => ReadComparison.product R L J NR NL hl hr

set_option backward.isDefEq.respectTransparency false in
omit rF in
theorem ReadComparison.branchTrace (p : ReadComparison A B) :
    let e := p.branchEquiv
    let G := (fr B).relabel e.symm e.symm.injective ((fr B).label ∘ e)
      (fun x => congrArg (fr B).label (e.apply_symm_apply x).symm)
    RawSingletonTrace (fr A) G (p.coefficient (T:=T)) (lift p).hom.native := by
  intro e G
  have h := p.accumulate_trace R L J NL hl id e.symm Function.injective_id e.symm.injective
    (fun x => (e.symm_apply_apply x).symm) (fr A).label ((fr B).label ∘ e)
    (fun _ => rfl) (fun x => congrArg (fr B).label (e.apply_symm_apply x).symm)
    (p.coefficient (T:=T)) (fun _ => HEq.rfl)
  exact h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
local notation "ph" => binaryFubini R L J N NR NL hl hr m mi h j unit_middle

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5800000 in
/-- Separate tensoring and joint product of ordered structural comparisons
give the same literal native square against the original binary Fubini. -/
theorem ReadComparison.binaryFubini_natural (p : ReadComparison A B) (q : ReadComparison D E) :
    (independentAugMap R L (J.ρ I) N NR NL hl hr (lift p).hom (lift q).hom).comp (ph B E).hom =
      (ph A D).hom.comp (lift (rd p q)).hom := by
  let r := rd p q
  let Ω := A.Branch × D.Branch
  let ep := p.branchEquiv
  let eq := q.branchEquiv
  let u := Equiv.prodCongr ep eq
  let a (z : Ω) := A.V z.1.1
  let b (z : Ω) := A.A z.1.1 z.1.2
  let c (z : Ω) := D.V z.2.1
  let d (z : Ω) := D.A z.2.1 z.2.2
  let a' (z : Ω) := B.V (ep z.1).1
  let b' (z : Ω) := B.A (ep z.1).1 (ep z.1).2
  let c' (z : Ω) := E.V (eq z.2).1
  let d' (z : Ω) := E.A (eq z.2).1 (eq z.2).2
  let P (z : Ω) : a z ⟶ a' z := (p.parent.coefficient z.1.1).hom
  let Q (z : Ω) : b z ⟶ b' z := ((p.child z.1.1).coefficient z.1.2).hom
  let S (z : Ω) : c z ⟶ c' z := (q.parent.coefficient z.2.1).hom
  let W (z : Ω) : d z ⟶ d' z := ((q.child z.2.1).coefficient z.2.2).hom
  let F (z : Ω) := T.obj (T.obj (a z) (b z)) (T.obj (c z) (d z))
  let G (z : Ω) := T.obj (T.obj (a' z) (b' z)) (T.obj (c' z) (d' z))
  let H (z : Ω) := T.obj (T.obj (a z) (c z)) (T.obj (b z) (d z))
  let K (z : Ω) := T.obj (T.obj (a' z) (c' z)) (T.obj (b' z) (d' z))
  let p₀ (z : Ω) : F z ⟶ G z := T.map (T.map (P z) (Q z)) (T.map (S z) (W z))
  let q₀ (z : Ω) : G z ⟶ K z := m.cell (a' z) (b' z) (c' z) (d' z)
  let r₀ (z : Ω) : F z ⟶ H z := m.cell (a z) (b z) (c z) (d z)
  let s₀ (z : Ω) : H z ⟶ K z := T.map (T.map (P z) (S z)) (T.map (Q z) (W z))
  let z₀ := (fr A).tensor T (fr D)
  let z₁ := ((fr B).tensor T (fr E)).relabel u.symm u.symm.injective G
    (fun z => congrArg ((fr B).tensor T (fr E)).label (u.apply_symm_apply z).symm)
  let z₂ := jointFrame R L J A D
  let z₃ := (jointFrame R L J B E).relabel u.symm u.symm.injective K
    (fun z => congrArg (jointFrame R L J B E).label (u.apply_symm_apply z).symm)
  have hp : RawSingletonTrace z₀ z₁ p₀
      (independentAugMap R L (J.ρ I) N NR NL hl hr (lift p).hom (lift q).hom).native :=
    ((p.branchTrace R L J NL hl).tensor R L hl hr (q.branchTrace R L J NL hl)).changeFrame
      (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have hq : RawSingletonTrace z₁ z₃ q₀ (ph B E).hom.native :=
    (binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr B E).relabel u.symm u.symm.injective
      G K (fun z => congrArg ((fr B).tensor T (fr E)).label (u.apply_symm_apply z).symm)
      (fun z => congrArg (jointFrame R L J B E).label (u.apply_symm_apply z).symm)
      q₀ (fun z => by
        have h := DependentFubiniTree.medial_cell_heq m
          (congrArg (fun z : B.Branch × E.Branch => B.V z.1.1) (u.apply_symm_apply z).symm)
          (congrArg (fun z : B.Branch × E.Branch => B.A z.1.1 z.1.2) (u.apply_symm_apply z).symm)
          (congrArg (fun z : B.Branch × E.Branch => E.V z.2.1) (u.apply_symm_apply z).symm)
          (congrArg (fun z : B.Branch × E.Branch => E.A z.2.1 z.2.2) (u.apply_symm_apply z).symm)
        exact h)
  have hr' : RawSingletonTrace z₀ z₂ r₀ (ph A D).hom.native :=
    binaryFubini_trace R L J N NR NL m mi h j unit_middle hl hr A D
  have hs : RawSingletonTrace z₂ z₃ s₀ (lift r).hom.native := by
    let f := jointRead A D
    let g := (jointRead B E).trans u.symm
    have k (z : (prd A D).Branch) : f z = g (r.parent.read z.1,(r.child z.1).read z.2) :=
      (u.symm_apply_apply (f z)).symm
    have t := r.accumulate_trace R L J NL hl f g f.injective g.injective k H K (fun _ => rfl)
      (fun z => congrArg (jointFrame R L J B E).label (u.apply_symm_apply (jointRead B E z)).symm)
      s₀ (fun _ => HEq.rfl)
    exact t.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  apply AugHom.ext
  exact (hp.comp hq).eq (hr'.comp hs) (fun i => m.nat (P (z₃.read i)) (Q (z₃.read i)) (S (z₃.read i)) (W (z₃.read i)))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.OrderedDependentAugData
