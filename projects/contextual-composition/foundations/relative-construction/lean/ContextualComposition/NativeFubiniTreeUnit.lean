module
public import ContextualComposition.NativeFubiniTreeSwap
@[expose] public section

/-! Right unit deletion at a root over an arbitrary child tree.
Left deletion can be executed by swapping and then deleting the unit. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C]
variable {T : Bi (coeff (C:=C))} {I : C} {S : Bi (coeff (C:=C))} {Z : C}
variable (R : Gather S T Z) (J : UnitCompat R I) (m : Middle T I)

set_option backward.isDefEq.respectTransparency false in
theorem medialRightUnit_after [IsIso (J.ρ I)] (law : MedialRightUnit R J m) {x a b : C}
    (p : x ⟶ T.obj a b) :
    (T.map p (inv (J.ρ I)) ≫ m.cell a b I I) ≫ T.map (J.ρ a) (J.ρ b) = J.ρ x ≫ p := by
  let K := coeff (C:=C)
  have k : T.map p (inv (J.ρ I)) ≫ T.map (𝟙 (T.obj a b)) (J.ρ I) = T.map p (𝟙 I) := by
    change K.seq _ _ = _
    rw [← T.map_seq, K.seq_id, show K.seq (inv (J.ρ I)) (J.ρ I) = K.id I from IsIso.inv_hom_id (J.ρ I)]
  rw [Category.assoc, law, reassoc_of% k]
  exact J.natural p

namespace DependentFubiniTree
open OrderedDependentAugData
variable [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable (R₀ : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J₀ : UnitCompat R₀ I)
variable (N : GridBinary (symmetricCross (C:=C)) R₀ L) (NR : GatherOuterNat R₀) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R₀ b)
variable (ιρ : ∀ c, IsIso (J₀.ρ c))
variable (a : DependentFubiniTree I)
local notation "aa" => DependentFubiniTree.fork a DependentFubiniTree.unit
local notation "inp" => jointInput R₀ L J₀
local notation "sep" => separate R₀ L J₀
local notation "wc" => wordCell R₀ L J₀
local notation "lc" => separateCoeff (T:=T)
local notation "jc" => jointCoeff (T:=T)
local notation "sr" => independentRightUnit_read R₀ L J₀ (lc a) a.word (wc a) (hl:=hl) (iρ:=ιρ)

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateRightUnitIso : NativeAugmentedIso (sep aa) (sep a) :=
  ((sr).toIso (word_nodup aa)).retarget
    (separate_word_eq R₀ L J₀ aa).symm (separate_word_eq R₀ L J₀ a).symm

set_option backward.isDefEq.respectTransparency false in
omit rF in
theorem separateRightUnit_trace :
    let e := singletonRightRead a.Address
    let F := (aa).separateTagFrame R₀ L J₀
    let G := (a.separateTagFrame R₀ L J₀).relabel e.symm e.symm.injective (lc a ∘ e) (fun _ => rfl)
    RawSingletonTrace F G (fun z => J₀.ρ (lc a z.1)) (separateRightUnitIso R₀ L J₀ hl ιρ a).hom.native := by
  intro e F G
  let u := sr
  let e₀ := congrArg Aug.base (separate_word_eq R₀ L J₀ aa)
  let e₁ := congrArg Aug.base (separate_word_eq R₀ L J₀ a)
  let F₀ := rawWordFrame (lc aa) (word aa) (word_nodup aa)
  let G₀ := (rawWordFrame (lc a) (word a) (word_nodup a)).relabel e.symm e.symm.injective (lc a ∘ e) (fun _ => rfl)
  have h : RawSingletonTrace F₀ G₀ (fun z => J₀.ρ (lc a z.1)) (u.toIso (word_nodup aa)).hom.native :=
    (u.toIso_trace (word_nodup aa) (word_nodup a)).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have k : HEq (u.toIso (word_nodup aa)).hom.native (separateRightUnitIso R₀ L J₀ hl ιρ a).hom.native := by
    unfold separateRightUnitIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  exact h.retarget e₀.symm e₁.symm k
    (rawFrame_read_reverse F F₀ e₀ (separateFrame_word R₀ L J₀ aa))
    (rawFrame_read_reverse G G₀ e₁ (fun i => congrArg e.symm (separateFrame_word R₀ L J₀ a i))) (fun _ => HEq.rfl)

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R₀ L) (j : MedialInner m R₀ L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R₀ J₀ = unitCollapse R₀ J₀)
variable [IsIso (J₀.ρ I)]
local notation "ph" => comparison R₀ L J₀ N NR NL hl hr m mi h j unit_middle

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem rightUnit_cell_heq {a b : C} (e : a = b) : HEq (J.ρ a) (J.ρ b) := by
  subst b
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 7500000 in
theorem comparison_runit (law : MedialRightUnit R₀ J₀ m) :
    (separateRightUnitIso R₀ L J₀ hl ιρ a).hom.comp (ph a).hom =
      (ph aa).hom.comp ((jointRightUnitComparison R₀ L J₀ hl ιρ (inp a)).accumulate R₀ L J₀ NL hl).hom := by
  let Ω := a.Address × PUnit.{u+1}
  let e := singletonRightRead a.Address
  let F := (aa).separateTagFrame R₀ L J₀
  let G := (a.separateTagFrame R₀ L J₀).relabel e.symm e.symm.injective (lc a ∘ e) (fun _ => rfl)
  let H := (aa).jointTagFrame R₀ L J₀
  let K := (a.jointTagFrame R₀ L J₀).relabel e.symm e.symm.injective (jc a ∘ e) (fun _ => rfl)
  let x₀ := (separateRightUnitIso R₀ L J₀ hl ιρ a).hom
  let x₁ := (ph a).hom
  let y₀ := (ph aa).hom
  let v := jointRightUnitComparison R₀ L J₀ hl ιρ (inp a)
  let y₁ := (v.accumulate R₀ L J₀ NL hl).hom
  let p (z : Ω) : F.label z ⟶ G.label z := J₀.ρ (lc a z.1)
  let q (z : Ω) : G.label z ⟶ K.label z := coefficient (m:=m) (inv (J₀.ρ I)) a z.1
  let r (z : Ω) : F.label z ⟶ H.label z := coefficient (m:=m) (inv (J₀.ρ I)) aa z
  let p₀ (z : Ω) := parentCoeff (T:=T) a z.1
  let q₀ (z : Ω) := childCoeff (T:=T) a z.1
  let s (z : Ω) : H.label z ⟶ K.label z := T.map (J₀.ρ (p₀ z)) (J₀.ρ (q₀ z))
  have hp : RawSingletonTrace F G p x₀.native := separateRightUnit_trace R₀ L J₀ hl ιρ a
  have hq : RawSingletonTrace G K q x₁.native :=
    (comparison_trace R₀ L J₀ N NR NL hl hr m mi h j unit_middle a).relabel e.symm e.symm.injective
      (lc a ∘ e) (jc a ∘ e) (fun _ => rfl) (fun _ => rfl) q (fun _ => HEq.rfl)
  have hr' : RawSingletonTrace F H r y₀.native :=
    comparison_trace R₀ L J₀ N NR NL hl hr m mi h j unit_middle aa
  have hs : RawSingletonTrace H K s y₁.native := by
    let f := branchRead R₀ L J₀ aa
    let g := (branchRead R₀ L J₀ a).trans e.symm
    let u (z : (inp aa).Branch) := ((z.1.1,z.2.1) : (inp a).Branch)
    have k (z : (inp aa).Branch) : f z = g (v.parent.read z.1,(v.child z.1).read z.2) := rfl
    have h₀ (z : (inp aa).Branch) : HEq
        (T.map (v.parent.coefficient z.1).hom ((v.child z.1).coefficient z.2).hom) (s (f z)) := by
      have ep := parentCoeff_read R₀ L J₀ a (u z)
      have fp := childCoeff_read R₀ L J₀ a (u z)
      exact biMap_heq (T:=T) (congrArg (fun x => T.obj x I) ep) ep (congrArg (fun x => T.obj x I) fp) fp
        (rightUnit_cell_heq R₀ J₀ ep) (rightUnit_cell_heq R₀ J₀ fp)
    let hV (z : (inp aa).Branch) := congrArg₂ T.obj (parentCoeff_read R₀ L J₀ aa z) (childCoeff_read R₀ L J₀ aa z)
    let hW (z : (inp a).Branch) := congrArg₂ T.obj (parentCoeff_read R₀ L J₀ a z) (childCoeff_read R₀ L J₀ a z)
    have zz := v.accumulate_trace R₀ L J₀ NL hl f g f.injective g.injective k H.label K.label hV hW s h₀
    exact zz.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  apply AugHom.ext
  exact (hp.comp hq).eq (hr'.comp hs) (fun i =>
    let z := K.read i
    (medialRightUnit_after R₀ J₀ m law (coefficient (m:=m) (inv (J₀.ρ I)) a z.1)).symm)

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
