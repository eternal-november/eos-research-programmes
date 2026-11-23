module
public import ContextualComposition.NativeFubiniTreeAssocMove
@[expose] public section

/-! Literal symmetry of arbitrary child trees, including unit subtrees. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C]
variable {T : Bi (coeff (C:=C))} {I : C}
variable (P : TensorPrimitive T) (m : Middle T I)

set_option backward.isDefEq.respectTransparency false in
theorem medialSwap_after (law : MedialSwap P m) {x y : C} (a b c d : C)
    (p : x ⟶ T.obj a b) (q : y ⟶ T.obj c d) :
    (T.map p q ≫ m.cell a b c d) ≫ T.map (P.swap a c) (P.swap b d) =
      P.swap x y ≫ T.map q p ≫ m.cell c d a b := by
  have n : T.map p q ≫ P.swap (T.obj a b) (T.obj c d) = P.swap x y ≫ T.map q p := P.swap_nat p q
  rw [Category.assoc, law, reassoc_of% n]

namespace DependentFubiniTree
open OrderedDependentAugData
variable [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C:=C)
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable (Q : PrimitiveLinearity R L P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (swap_unit : P.swap I I ≫ J.ρ I = J.ρ I) (ι : ∀ a b, IsIso (P.swap a b))
variable (a b : DependentFubiniTree I)
local notation "aa" => DependentFubiniTree.fork a b
local notation "bb" => DependentFubiniTree.fork b a
local notation "inp" => jointInput R L J
local notation "sep" => separate R L J
local notation "wc" => wordCell R L J
local notation "lc" => separateCoeff (T:=T)
local notation "jc" => jointCoeff (T:=T)
local notation "sr" => independentSwapReadComparison R L P Q N (lc a) (lc b) a.word b.word J swap_unit ι (wc a) (wc b)

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateSwapIso : NativeAugmentedIso (sep aa) (sep bb) :=
  ((sr).toIso (word_nodup aa)).retarget
    (separate_word_eq R L J aa).symm (separate_word_eq R L J bb).symm

set_option backward.isDefEq.respectTransparency false in
omit lF rF in
theorem separateSwap_trace :
    let e := Equiv.prodComm a.Address b.Address
    let F := (aa).separateTagFrame R L J
    let G := ((bb).separateTagFrame R L J).relabel e.symm e.symm.injective (lc bb ∘ e) (fun _ => rfl)
    RawSingletonTrace F G (fun z => P.swap (lc a z.1) (lc b z.2))
      (separateSwapIso P R L J N Q swap_unit ι a b).hom.native := by
  intro e F G
  let u := sr
  let e₀ := congrArg Aug.base (separate_word_eq R L J aa)
  let e₁ := congrArg Aug.base (separate_word_eq R L J bb)
  let F₀ := rawWordFrame (lc aa) (word aa) (word_nodup aa)
  let G₀ := (rawWordFrame (lc bb) (word bb) (word_nodup bb)).relabel e.symm e.symm.injective
    (lc bb ∘ e) (fun _ => rfl)
  have h : RawSingletonTrace F₀ G₀ (fun z => P.swap (lc a z.1) (lc b z.2))
      (u.toIso (word_nodup aa)).hom.native :=
    (u.toIso_trace (word_nodup aa) (word_nodup bb)).changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have k : HEq (u.toIso (word_nodup aa)).hom.native
      (separateSwapIso P R L J N Q swap_unit ι a b).hom.native := by
    unfold separateSwapIso
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  exact h.retarget e₀.symm e₁.symm k
    (rawFrame_read_reverse F F₀ e₀ (separateFrame_word R L J aa))
    (rawFrame_read_reverse G G₀ e₁ (fun i => congrArg e.symm (separateFrame_word R L J bb i))) (fun _ => HEq.rfl)

variable (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]
local notation "ph" => comparison R L J N NR NL hl hr m mi h j unit_middle

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem swap_cell_heq {a b a' b' : C} (e : a = a') (f : b = b') :
    HEq (P.swap a b) (P.swap a' b') := by
  subst a'; subst b'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 7500000 in
theorem comparison_swap (law : MedialSwap P m) :
    (separateSwapIso P R L J N Q swap_unit ι a b).hom.comp (ph bb).hom =
      (ph aa).hom.comp ((jointSwapComparison R L J P N Q swap_unit ι (inp a) (inp b)).accumulate R L J NL hl).hom := by
  let Ω := a.Address × b.Address
  let e := Equiv.prodComm a.Address b.Address
  let F := (aa).separateTagFrame R L J
  let G := ((bb).separateTagFrame R L J).relabel e.symm e.symm.injective (lc bb ∘ e) (fun _ => rfl)
  let H := (aa).jointTagFrame R L J
  let K := ((bb).jointTagFrame R L J).relabel e.symm e.symm.injective (jc bb ∘ e) (fun _ => rfl)
  let x₀ := (separateSwapIso P R L J N Q swap_unit ι a b).hom
  let x₁ := (ph bb).hom
  let y₀ := (ph aa).hom
  let v := jointSwapComparison R L J P N Q swap_unit ι (inp a) (inp b)
  let y₁ := (v.accumulate R L J NL hl).hom
  let p (z : Ω) : F.label z ⟶ G.label z := P.swap (lc a z.1) (lc b z.2)
  let q (z : Ω) : G.label z ⟶ K.label z := coefficient (m:=m) (inv (J.ρ I)) bb (e z)
  let r (z : Ω) : F.label z ⟶ H.label z := coefficient (m:=m) (inv (J.ρ I)) aa z
  let p₀ (z : Ω) := parentCoeff (T:=T) a z.1
  let p₁ (z : Ω) := parentCoeff (T:=T) b z.2
  let q₀ (z : Ω) := childCoeff (T:=T) a z.1
  let q₁ (z : Ω) := childCoeff (T:=T) b z.2
  let s (z : Ω) : H.label z ⟶ K.label z := T.map (P.swap (p₀ z) (p₁ z)) (P.swap (q₀ z) (q₁ z))
  have hp : RawSingletonTrace F G p x₀.native := separateSwap_trace P R L J N Q swap_unit ι a b
  have hq : RawSingletonTrace G K q x₁.native :=
    (comparison_trace R L J N NR NL hl hr m mi h j unit_middle bb).relabel e.symm e.symm.injective
      (lc bb ∘ e) (jc bb ∘ e) (fun _ => rfl) (fun _ => rfl)
      q (fun z => by
        change HEq (coefficient (m:=m) (inv (J.ρ I)) bb z)
          (coefficient (m:=m) (inv (J.ρ I)) bb (e (e.symm z)))
        rw [e.apply_symm_apply])
  have hr' : RawSingletonTrace F H r y₀.native :=
    comparison_trace R L J N NR NL hl hr m mi h j unit_middle aa
  have hs : RawSingletonTrace H K s y₁.native := by
    let f := branchRead R L J aa
    let g := (branchRead R L J bb).trans e.symm
    let u (z : (inp aa).Branch) := ((z.1.1,z.2.1) : (inp a).Branch)
    let w (z : (inp aa).Branch) := ((z.1.2,z.2.2) : (inp b).Branch)
    have k (z : (inp aa).Branch) : f z = g (v.parent.read z.1,(v.child z.1).read z.2) := rfl
    have h₀ (z : (inp aa).Branch) : HEq
        (T.map (v.parent.coefficient z.1).hom ((v.child z.1).coefficient z.2).hom) (s (f z)) := by
      have ep := parentCoeff_read R L J a (u z)
      have eq := parentCoeff_read R L J b (w z)
      have fp := childCoeff_read R L J a (u z)
      have fq := childCoeff_read R L J b (w z)
      exact biMap_heq (T:=T) (congrArg₂ T.obj ep eq) (congrArg₂ T.obj eq ep)
        (congrArg₂ T.obj fp fq) (congrArg₂ T.obj fq fp) (swap_cell_heq P ep eq) (swap_cell_heq P fp fq)
    let hV (z : (inp aa).Branch) := congrArg₂ T.obj (parentCoeff_read R L J aa z) (childCoeff_read R L J aa z)
    let hW (z : (inp bb).Branch) := congrArg₂ T.obj (parentCoeff_read R L J bb z) (childCoeff_read R L J bb z)
    have zz := v.accumulate_trace R L J NL hl f g f.injective g.injective k H.label K.label hV hW s h₀
    exact zz.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  apply AugHom.ext
  exact (hp.comp hq).eq (hr'.comp hs) (fun i =>
    let z := K.read i
    (medialSwap_after P m law (p₀ z) (q₀ z) (p₁ z) (q₁ z)
      (coefficient (m:=m) (inv (J.ρ I)) a z.1) (coefficient (m:=m) (inv (J.ρ I)) b z.2)).symm)

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
