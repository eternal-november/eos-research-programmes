module
public import ContextualComposition.NativeFubiniTreeWord
@[expose] public section

/-! Rebracket at a root whose three children may themselves be arbitrary
dependent Fubini trees. Whiskering is a separate operation. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C]
variable {T : Bi (coeff (C:=C))} {I : C}
variable (P : TensorPrimitive T) (m : Middle T I)

set_option backward.isDefEq.respectTransparency false in
theorem medialRegroup_after (law : MedialRegroup P m) {x y z : C} (a b c d e f : C)
    (p : x ⟶ T.obj a b) (q : y ⟶ T.obj c d) (r : z ⟶ T.obj e f) :
    (T.map (T.map p q ≫ m.cell a b c d) r ≫ m.cell (T.obj a c) (T.obj b d) e f) ≫
      T.map (P.assoc a c e) (P.assoc b d f) =
    P.assoc x y z ≫ (T.map p (T.map q r ≫ m.cell c d e f) ≫ m.cell a b (T.obj c e) (T.obj d f)) := by
  let K := coeff (C:=C)
  have e₁ : T.map (T.map p q ≫ m.cell a b c d) r =
      T.map (T.map p q) r ≫ T.map (m.cell a b c d) (𝟙 (T.obj e f)) := by
    change _ = K.seq _ _
    rw [← T.map_seq, K.seq_id]
  have e₂ : T.map p (T.map q r ≫ m.cell c d e f) =
      T.map p (T.map q r) ≫ T.map (𝟙 (T.obj a b)) (m.cell c d e f) := by
    change _ = K.seq _ _
    rw [← T.map_seq, K.seq_id]
  have n : T.map (T.map p q) r ≫ P.assoc (T.obj a b) (T.obj c d) (T.obj e f) =
      P.assoc x y z ≫ T.map p (T.map q r) := P.assoc_nat p q r
  simp only [e₁,e₂, Category.assoc]
  rw [law, reassoc_of% n]

variable [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (ι : ∀ a b d, IsIso (P.assoc a b d))

section Word
variable {X Y W : Type u} (A : X → C) (B : Y → C) (D : W → C)
variable (xs : List X) (ys : List Y) (ws : List W)
variable (a : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) A xs ⟶ I)
variable (b : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) B ys ⟶ I)
variable (d : fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) D ws ⟶ I)

set_option backward.isDefEq.respectTransparency false in
include NR NL Q U hl hr ι in
noncomputable def independentAssocRead :
    WordAugReadComparison (crossLabel T (crossLabel T A B) D) (crossLabel T A (crossLabel T B D))
      ((xs.product ys).product ws) (xs.product (ys.product ws))
      (independentAssocLeftAug R L J A B D xs ys ws a b d)
      (independentAssocRightAug R L J A B D xs ys ws a b d) := by
  let φ (x : (X × Y) × W) : T.obj (T.obj (A x.1.1) (B x.1.2)) (D x.2) ≅
      T.obj (A x.1.1) (T.obj (B x.1.2) (D x.2)) := by
    let _ := ι (A x.1.1) (B x.1.2) (D x.2)
    exact asIso (P.assoc (A x.1.1) (B x.1.2) (D x.2))
  exact WordAugReadComparison.ofOrderPreserving tripleRetag
    (tripleRetag_word xs (fun _ => ys) (fun _ _ => ws)) φ _ _
    (independentAssoc_preserves_pullback R L J P NR NL Q U hl hr A B D xs ys ws a b d)

end Word

namespace OrderedDependentAugData
local notation "prd" => product R L J
set_option backward.isDefEq.respectTransparency false in
noncomputable def jointAssocRead (A B D : OrderedDependentAugData I) :
    ReadComparison (prd (prd A B) D) (prd A (prd B D)) where
  parent := independentAssocRead P R L J NR NL Q U hl hr ι A.V B.V D.V A.xs B.xs D.xs A.ε B.ε D.ε
  child x := independentAssocRead P R L J NR NL Q U hl hr ι (A.A x.1.1) (B.A x.1.2) (D.A x.2)
    (A.us x.1.1) (B.us x.1.2) (D.us x.2) (A.δ x.1.1) (B.δ x.1.2) (D.δ x.2)

end OrderedDependentAugData

namespace DependentFubiniTree
open OrderedDependentAugData
variable (a b d : DependentFubiniTree I)
local notation "lc" => separateCoeff (T:=T)
local notation "sep" => separate R L J
local notation "wc" => wordCell R L J
local notation "inp" => jointInput R L J
local notation "aa" => DependentFubiniTree.fork (DependentFubiniTree.fork a b) d
local notation "bb" => DependentFubiniTree.fork a (DependentFubiniTree.fork b d)

set_option backward.isDefEq.respectTransparency false in
noncomputable def separateAssoc :
    NativeAugmentedIso (sep aa) (sep bb) :=
  (independentAssocRead P R L J NR NL Q U hl hr ι (lc a) (lc b) (lc d)
    a.word b.word d.word (wc a) (wc b) (wc d)).toIso (word_nodup aa) |>.retarget
      (separate_word_eq R L J aa).symm (separate_word_eq R L J bb).symm

set_option backward.isDefEq.respectTransparency false in
theorem separateAssoc_trace :
    let e := tripleRetag (X:=a.Address) (Y:=b.Address) (W:=d.Address)
    let F := ((aa).separateTagFrame R L J).relabel e e.injective (lc aa ∘ e.symm) (fun _ => rfl)
    RawSingletonTrace F ((bb).separateTagFrame R L J)
      (fun z => P.assoc (lc a z.1) (lc b z.2.1) (lc d z.2.2))
      (separateAssoc P R L J NR NL Q U hl hr ι a b d).hom.native := by
  intro e F
  let p := independentAssocRead P R L J NR NL Q U hl hr ι (lc a) (lc b) (lc d)
    a.word b.word d.word (wc a) (wc b) (wc d)
  let e₀ := congrArg Aug.base (separate_word_eq R L J aa)
  let e₁ := congrArg Aug.base (separate_word_eq R L J bb)
  have h := (p.toIso_trace (word_nodup aa) (word_nodup bb)).relabel e e.injective
    (lc aa ∘ e.symm) (lc bb) (fun _ => rfl) (fun _ => rfl)
    (fun z => P.assoc (lc a z.1) (lc b z.2.1) (lc d z.2.2)) (fun _ => HEq.rfl)
  let F₀ := (rawWordFrame (lc aa) (aa).word (word_nodup aa)).relabel e e.injective (lc aa ∘ e.symm) (fun _ => rfl)
  let G₀ := rawWordFrame (lc bb) (bb).word (word_nodup bb)
  have h' : RawSingletonTrace F₀ G₀ (fun z => P.assoc (lc a z.1) (lc b z.2.1) (lc d z.2.2))
      (p.toIso (word_nodup aa)).hom.native :=
    h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  have k : HEq (p.toIso (word_nodup aa)).hom.native
      (separateAssoc P R L J NR NL Q U hl hr ι a b d).hom.native := by
    unfold separateAssoc
    exact (NativeAugmentedIso.retarget_native_heq _ _ _).symm
  exact h'.retarget e₀.symm e₁.symm k
    (rawFrame_read_reverse F F₀ e₀ (fun i => congrArg e (separateFrame_word R L J aa i)))
    (rawFrame_read_reverse ((bb).separateTagFrame R L J) G₀ e₁ (separateFrame_word R L J bb))
    (fun _ => HEq.rfl)

variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]
local notation "ph" => comparison R L J N NR NL hl hr m mi h j unit_middle

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem assoc_cell_heq {a b c a' b' c' : C} (e : a = a') (f : b = b') (g : c = c') :
    HEq (P.assoc a b c) (P.assoc a' b' c') := by
  subst a'; subst b'; subst c'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 7700000 in
/-- Literal Fubini for arbitrary subtrees commutes with a root reassociation. -/
theorem comparison_assoc (law : MedialRegroup P m) :
    (separateAssoc P R L J NR NL Q U hl hr ι a b d).hom.comp (ph bb).hom =
      (ph aa).hom.comp ((jointAssocRead P R L J NR NL Q U hl hr ι (inp a) (inp b) (inp d)).accumulate
        R L J NL hl).hom := by
  let Ω := a.Address × b.Address × d.Address
  let e := tripleRetag (X:=a.Address) (Y:=b.Address) (W:=d.Address)
  let F := ((aa).separateTagFrame R L J).relabel e e.injective (lc aa ∘ e.symm) (fun _ => rfl)
  let G := (bb).separateTagFrame R L J
  let H := ((aa).jointTagFrame R L J).relabel e e.injective (jointCoeff (T:=T) aa ∘ e.symm) (fun _ => rfl)
  let K := (bb).jointTagFrame R L J
  let x₀ := (separateAssoc P R L J NR NL Q U hl hr ι a b d).hom
  let x₁ := (ph bb).hom
  let y₀ := (ph aa).hom
  let v := jointAssocRead P R L J NR NL Q U hl hr ι (inp a) (inp b) (inp d)
  let y₁ := (v.accumulate R L J NL hl).hom
  let pp (z : Ω) : F.label z ⟶ G.label z := P.assoc (lc a z.1) (lc b z.2.1) (lc d z.2.2)
  let qq (z : Ω) : G.label z ⟶ K.label z := coefficient (m:=m) (inv (J.ρ I)) bb z
  let rr (z : Ω) : F.label z ⟶ H.label z := coefficient (m:=m) (inv (J.ρ I)) aa (e.symm z)
  let p₀ (z : Ω) := parentCoeff (T:=T) a z.1
  let p₁ (z : Ω) := parentCoeff (T:=T) b z.2.1
  let p₂ (z : Ω) := parentCoeff (T:=T) d z.2.2
  let q₀ (z : Ω) := childCoeff (T:=T) a z.1
  let q₁ (z : Ω) := childCoeff (T:=T) b z.2.1
  let q₂ (z : Ω) := childCoeff (T:=T) d z.2.2
  let ss (z : Ω) : H.label z ⟶ K.label z :=
    T.map (P.assoc (p₀ z) (p₁ z) (p₂ z)) (P.assoc (q₀ z) (q₁ z) (q₂ z))
  have hp : RawSingletonTrace F G pp x₀.native := separateAssoc_trace P R L J NR NL Q U hl hr ι a b d
  have hq : RawSingletonTrace G K qq x₁.native :=
    comparison_trace R L J N NR NL hl hr m mi h j unit_middle bb
  have hr' : RawSingletonTrace F H rr y₀.native :=
    (comparison_trace R L J N NR NL hl hr m mi h j unit_middle aa).relabel e e.injective
      (lc aa ∘ e.symm) (jointCoeff (T:=T) aa ∘ e.symm) (fun _ => rfl) (fun _ => rfl)
      rr (fun z => by
        change HEq (coefficient (m:=m) (inv (J.ρ I)) aa z)
          (coefficient (m:=m) (inv (J.ρ I)) aa (e.symm (e z)))
        rw [e.symm_apply_apply])
  have hs : RawSingletonTrace H K ss y₁.native := by
    let f := (branchRead R L J aa).trans e
    let g := branchRead R L J bb
    let u (z : (inp aa).Branch) := ((z.1.1.1,z.2.1.1) : (inp a).Branch)
    let w (z : (inp aa).Branch) := ((z.1.1.2,z.2.1.2) : (inp b).Branch)
    let t (z : (inp aa).Branch) := ((z.1.2,z.2.2) : (inp d).Branch)
    have k (z : (inp aa).Branch) : f z = g (v.parent.read z.1,(v.child z.1).read z.2) := rfl
    have h₀ (z : (inp aa).Branch) : HEq
        (T.map (v.parent.coefficient z.1).hom ((v.child z.1).coefficient z.2).hom) (ss (f z)) := by
      let A' := inp a
      let B' := inp b
      let D' := inp d
      have ep₀ := parentCoeff_read R L J a (u z)
      have ep₁ := parentCoeff_read R L J b (w z)
      have ep₂ := parentCoeff_read R L J d (t z)
      have eq₀ := childCoeff_read R L J a (u z)
      have eq₁ := childCoeff_read R L J b (w z)
      have eq₂ := childCoeff_read R L J d (t z)
      have e₀ := congrArg₂ T.obj (congrArg₂ T.obj ep₀ ep₁) ep₂
      have e₁ := congrArg₂ T.obj ep₀ (congrArg₂ T.obj ep₁ ep₂)
      have e₂ := congrArg₂ T.obj (congrArg₂ T.obj eq₀ eq₁) eq₂
      have e₃ := congrArg₂ T.obj eq₀ (congrArg₂ T.obj eq₁ eq₂)
      exact biMap_heq (T:=T) e₀ e₁ e₂ e₃ (assoc_cell_heq P ep₀ ep₁ ep₂) (assoc_cell_heq P eq₀ eq₁ eq₂)
    let hV (z : (inp aa).Branch) := congrArg₂ T.obj (parentCoeff_read R L J aa z) (childCoeff_read R L J aa z)
    let hW (z : (inp bb).Branch) := congrArg₂ T.obj (parentCoeff_read R L J bb z) (childCoeff_read R L J bb z)
    have zz := v.accumulate_trace R L J NL hl f g f.injective g.injective k H.label K.label hV hW ss h₀
    exact zz.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  apply AugHom.ext
  exact (hp.comp hq).eq (hr'.comp hs) (fun i =>
    let z := K.read i
    (medialRegroup_after P m law (p₀ z) (q₀ z) (p₁ z) (q₁ z) (p₂ z) (q₂ z)
      (coefficient (m:=m) (inv (J.ρ I)) a z.1) (coefficient (m:=m) (inv (J.ρ I)) b z.2.1)
      (coefficient (m:=m) (inv (J.ρ I)) d z.2.2)).symm)

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
