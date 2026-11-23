module
public import ContextualComposition.NativeFubiniTreeAssoc
@[expose] public section

/-! A reassociation at any finite depth is an actual commuting
Fubini square, not a rule limited to an isolated root triple. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)
variable (P : TensorPrimitive T) (Q : PrimitiveLinearity R L P) (U : AssocRightUnit R J P)
variable (ι : ∀ a b c, IsIso (P.assoc a b c))

set_option backward.isDefEq.respectTransparency false in
def wordIdentityRead {X : Type u} (V : X → C) (xs : List X)
    (p : fold 𝒮 Zₐ V xs ⟶ I) :
    WordAugReadComparison V V xs xs p p :=
  WordAugReadComparison.ofOrderPreserving (Equiv.refl X) (List.map_id xs) (fun x => Iso.refl (V x)) p p
    (by
      change act 𝒮 Zₐ (fun x => 𝟙 (V x)) xs ≫ eqToHom _ ≫ p = p
      have h : act 𝒮 Zₐ (fun x => 𝟙 (V x)) xs = 𝟙 _ := occurrence_act_id V xs
      rw [h, eqToHom_refl, Category.id_comp, Category.id_comp])

namespace OrderedDependentAugData
def identityRead (A : OrderedDependentAugData I) : ReadComparison A A where
  parent := wordIdentityRead A.V A.xs A.ε
  child x := wordIdentityRead (A.A x) (A.us x) (A.δ x)

set_option backward.isDefEq.respectTransparency false in
omit rF in
theorem identityRead_accumulate (A : OrderedDependentAugData I) :
    ((identityRead A).accumulate R L J NL hl).hom = AugHom.ident (A.accumulate R L J) := by
  let F := A.accFrame R L J
  let h := (identityRead A).branchTrace R L J NL hl
  have t : RawSingletonTrace F F (fun z => T.map (𝟙 (A.V z.1)) (𝟙 (A.A z.1 z.2)))
    ((identityRead A).accumulate R L J NL hl).hom.native :=
    h.changeFrame (fun _ => rfl) (fun _ => rfl) (fun _ => HEq.rfl)
  apply AugHom.ext
  exact t.eq (RawSingletonTrace.ident F) (fun z => T.map_id _ _)

end OrderedDependentAugData

def NativeAugmentedIso.reverse {A B : Aug ℙ I} (e : NativeAugmentedIso A B) :
    NativeAugmentedIso B A :=
  ⟨e.inv,e.hom,e.inv_hom,e.hom_inv⟩

namespace DependentFubiniTree
open OrderedDependentAugData

inductive AssocMove : DependentFubiniTree I → DependentFubiniTree I → Type _ where
  | root (a b c : DependentFubiniTree I) : AssocMove (.fork (.fork a b) c) (.fork a (.fork b c))
  | left {a b : DependentFubiniTree I} (p : AssocMove a b) (c : DependentFubiniTree I) : AssocMove (.fork a c) (.fork b c)
  | right (c : DependentFubiniTree I) {a b : DependentFubiniTree I} (p : AssocMove a b) : AssocMove (.fork c a) (.fork c b)

local notation "inp" => jointInput R L J
local notation "sep" => separate R L J
local notation "nm" => independentAugMap R L (J.ρ I) N NR NL hl hr
local notation "rp" => ReadComparison.product R L J NR NL hl hr
local notation "rc" => ReadComparison.accumulate R L J NL hl

noncomputable def AssocMove.joint {a b : DependentFubiniTree I} (p : AssocMove a b) :
    ReadComparison (inp a) (inp b) :=
  match p with
  | .root a b c => jointAssocRead P R L J NR NL Q U hl hr ι (inp a) (inp b) (inp c)
  | .left q c => rp q.joint (identityRead (inp c))
  | .right c q => rp (identityRead (inp c)) q.joint

noncomputable def AssocMove.separateIso {a b : DependentFubiniTree I} (p : AssocMove a b) :
    NativeAugmentedIso (sep a) (sep b) :=
  match p with
  | .root a b c => separateAssoc P R L J NR NL Q U hl hr ι a b c
  | .left q c => independentAugIso R L (J.ρ I) N NR NL hl hr q.separateIso (NativeAugmentedIso.ident (sep c))
  | .right c q => independentAugIso R L (J.ρ I) N NR NL hl hr (NativeAugmentedIso.ident (sep c)) q.separateIso

variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J)
variable [IsIso (J.ρ I)]
local notation "ph" => comparison R L J N NR NL hl hr m mi h j unit_middle
local notation "rs" => AssocMove.separateIso R L J N NR NL hl hr P Q U ι
local notation "rj" => AssocMove.joint R L J NR NL hl hr P Q U ι

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 5600000 in
theorem AssocMove.fubini {a b : DependentFubiniTree I} (p : AssocMove a b) (law : MedialRegroup P m) :
    (rs p).hom.comp (ph b).hom = (ph a).hom.comp (rc (rj p)).hom := by
  induction p with
  | root a b c => exact comparison_assoc P m R L J NR NL Q U hl hr ι a b c N mi h j unit_middle law
  | left q c ih =>
    have id₀ : (AugHom.ident (sep c)).comp (ph c).hom = (ph c).hom.comp (rc (identityRead (inp c))).hom := by
      rw [identityRead_accumulate R L J NL hl]
      exact (AugHom.ident_comp _).trans (AugHom.comp_ident _).symm
    exact comparison_fork_congr R L J N NR NL hl hr m mi h j unit_middle _ _ _ _ ih id₀
  | right c q ih =>
    have id₀ : (AugHom.ident (sep c)).comp (ph c).hom = (ph c).hom.comp (rc (identityRead (inp c))).hom := by
      rw [identityRead_accumulate R L J NL hl]
      exact (AugHom.ident_comp _).trans (AugHom.comp_ident _).symm
    exact comparison_fork_congr R L J N NR NL hl hr m mi h j unit_middle _ _ _ _ id₀ ih

set_option backward.isDefEq.respectTransparency false in
theorem AssocMove.fubini_inv {a b : DependentFubiniTree I} (p : AssocMove a b) (law : MedialRegroup P m) :
    (rs p).inv.comp (ph a).hom = (ph b).hom.comp (rc (rj p)).inv := by
  let x := rs p
  let y := rc (rj p)
  let a₀ := (ph a).hom
  let b₀ := (ph b).hom
  have e : x.hom.comp b₀ = a₀.comp y.hom :=
    AssocMove.fubini R L J N NR NL hl hr P Q U ι m mi h j unit_middle p law
  change x.inv.comp a₀ = b₀.comp y.inv
  calc
    _ = (x.inv.comp a₀).comp (y.hom.comp y.inv) := by rw [y.hom_inv, AugHom.comp_ident]
    _ = x.inv.comp ((a₀.comp y.hom).comp y.inv) := by rw [AugHom.comp_assoc, AugHom.comp_assoc]
    _ = _ := by rw [← e, ← AugHom.comp_assoc x.inv, ← AugHom.comp_assoc x.inv, x.inv_hom, AugHom.ident_comp]

/-- A finite addressed path of forward or reverse rotations at any
depth. Its two native realizations are chosen independently. -/
inductive AssocPath : DependentFubiniTree I → DependentFubiniTree I → Type _ where
  | ident (a : DependentFubiniTree I) : AssocPath a a
  | next {a b c : DependentFubiniTree I} (p : AssocMove a b) (q : AssocPath b c) : AssocPath a c
  | prev {a b c : DependentFubiniTree I} (p : AssocMove b a) (q : AssocPath b c) : AssocPath a c

local notation "acc" => OrderedDependentAugData.accumulate R L J

noncomputable def AssocPath.separateIso {a b : DependentFubiniTree I} (p : AssocPath a b) :
    NativeAugmentedIso (sep a) (sep b) :=
  match p with
  | .ident _ => NativeAugmentedIso.ident _
  | .next f g => (rs f).trans g.separateIso
  | .prev f g => (rs f).reverse.trans g.separateIso

noncomputable def AssocPath.jointIso {a b : DependentFubiniTree I} (p : AssocPath a b) :
    NativeAugmentedIso (acc (inp a)) (acc (inp b)) :=
  match p with
  | .ident _ => NativeAugmentedIso.ident _
  | .next f g => (rc (rj f)).trans g.jointIso
  | .prev f g => (rc (rj f)).reverse.trans g.jointIso

set_option backward.isDefEq.respectTransparency false in
theorem AssocPath.fubini {a b : DependentFubiniTree I} (p : AssocPath a b) (law : MedialRegroup P m) :
    (p.separateIso R L J N NR NL hl hr P Q U ι).hom.comp (ph b).hom =
      (ph a).hom.comp (p.jointIso R L J NR NL hl hr P Q U ι).hom := by
  induction p with
  | ident a => exact (AugHom.ident_comp _).trans (AugHom.comp_ident _).symm
  | @next a b c f g ih =>
    have h₀ := f.fubini R L J N NR NL hl hr P Q U ι m mi h j unit_middle law
    change ((rs f).hom.comp (g.separateIso R L J N NR NL hl hr P Q U ι).hom).comp (ph c).hom =
      (ph a).hom.comp ((rc (rj f)).hom.comp (g.jointIso R L J NR NL hl hr P Q U ι).hom)
    rw [AugHom.comp_assoc, ih, ← AugHom.comp_assoc, h₀, AugHom.comp_assoc]
  | @prev a b c f g ih =>
    have h₀ := f.fubini_inv R L J N NR NL hl hr P Q U ι m mi h j unit_middle law
    change ((rs f).inv.comp (g.separateIso R L J N NR NL hl hr P Q U ι).hom).comp (ph c).hom =
      (ph a).hom.comp ((rc (rj f)).inv.comp (g.jointIso R L J NR NL hl hr P Q U ι).hom)
    rw [AugHom.comp_assoc, ih, ← AugHom.comp_assoc, h₀, AugHom.comp_assoc]

end DependentFubiniTree
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
