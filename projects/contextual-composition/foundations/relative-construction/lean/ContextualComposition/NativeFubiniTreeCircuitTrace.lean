module
public import ContextualComposition.NativeTaggedTraceCompose
@[expose] public section

/-! Structural coefficient circuit evaluation and exact native traces.
The additive instance still constructs the native category; an explicit
second symmetric monoidal structure interprets the tensor circuits. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v w
variable {C : Type u} [cat : Category.{v} C] [add : MonoidalCategory C] [sa : SymmetricCategory C]
/-- Explicit interpretation of resource syntax, not an additive typeclass instance. -/
structure TensorSemantics (C : Type u) [Category.{v} C] where
  tensor : MonoidalCategory C
  symmetric : @SymmetricCategory C _ tensor

variable (M : TensorSemantics C)
set_option quotPrecheck false in
local notation "mul" => (M).tensor
set_option quotPrecheck false in
local notation "sm" => (M).symmetric
variable {Tag : Type w}
set_option quotPrecheck false in
local notation "Iₘ" => @MonoidalCategoryStruct.tensorUnit C cat (mul).toMonoidalCategoryStruct
local notation "Π" => binary (@Binary.ofMonoidal C cat mul)
set_option quotPrecheck false in
local notation "Tree" => @DependentFubiniTree C cat add sa (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct)
local notation "ℙ" => @standardPush C cat add sa
local notation "eval" => @TensorCircuit.evaluate C cat mul sm Tag

variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) (binary (@Binary.ofMonoidal C cat M.tensor)) (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) (binary (@Binary.ofMonoidal C cat M.tensor)) (𝟙_ C))
variable (J : UnitCompat R (@MonoidalCategoryStruct.tensorUnit C cat M.tensor.toMonoidalCategoryStruct))

local notation "fr" => separateTagFrame R L J
local notation "sep" => separate R L J
local notation "lc" => separateCoeff (T:=Π)

set_option backward.isDefEq.respectTransparency false in
structure CircuitTrace {a b : Tree} {s : Tagging Tag a} (p : TaggingTransport s b)
    (f : Hom (@standardPush C cat add sa) (separate R L J a).base (separate R L J b).base) where
  coefficient (z : a.Address) : lc a z ≅ lc b (p.read z)
  trace : NativeAddressTrace (fr a) (fr b) p.read coefficient f
  values (V : Tag → C) (z : a.Address) (hz : s.Matches (T:=Π) V z) :
    p.target.Matches (T:=Π) V (p.read z)
  circuit_eval (V : Tag → C) (z : a.Address) (hz : s.Matches (T:=Π) V z) :
    HEq (coefficient z).hom ((eval V p.circuit).hom)

set_option backward.isDefEq.respectTransparency false in
def CircuitTrace.ident {a : Tree} (s : Tagging Tag a) :
    CircuitTrace M R L J (TaggingTransport.ident s) (Hom.ident (separate R L J a).base) where
  coefficient z := Iso.refl (lc a z)
  trace := NativeAddressTrace.ident (fr a)
  values _ _ h := h
  circuit_eval V z hz := structural_id_heq (K:=coeff (C:=C)) (Tagging.matches_eval V mul a s z hz).symm

set_option backward.isDefEq.respectTransparency false in
def CircuitTrace.comp {a b c : Tree} {s : Tagging Tag a}
    {p : TaggingTransport s b} {q : TaggingTransport p.target c}
    {f : Hom (@standardPush C cat add sa) (separate R L J a).base (separate R L J b).base} {g : Hom (@standardPush C cat add sa) (separate R L J b).base (separate R L J c).base}
    (hf : CircuitTrace M R L J p f) (hg : CircuitTrace M R L J q g) :
    CircuitTrace M R L J (p.comp q) (f.comp g) where
  coefficient z := (hf.coefficient z).trans (hg.coefficient (p.read z))
  trace := NativeAddressTrace.comp hf.trace hg.trace
  values V z hz := hg.values V (p.read z) (hf.values V z hz)
  circuit_eval V z hz := by
    let y := p.read z
    let w := q.read y
    have hy := hf.values V z hz
    have hw := hg.values V y hy
    have e := (Tagging.matches_eval V mul a s z hz).symm
    have d := (Tagging.matches_eval V mul b p.target y hy).symm
    have k := (Tagging.matches_eval V mul c q.target w hw).symm
    exact structural_seq_heq (K:=coeff (C:=C)) e d k (hf.circuit_eval V z hz) (hg.circuit_eval V y hy)

set_option backward.isDefEq.respectTransparency false in
def CircuitTrace.tensor {a b c d : Tree} {s : Tagging Tag a} {t : Tagging Tag c}
    {p : TaggingTransport s b} {q : TaggingTransport t d}
    {f : Hom (@standardPush C cat add sa) (separate R L J a).base (separate R L J b).base} {g : Hom (@standardPush C cat add sa) (separate R L J c).base (separate R L J d).base}
    [lF : ∀ a : C, (leftFactor (binary (@Binary.ofMonoidal C cat (M).tensor)) a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=binary (@Binary.ofMonoidal C cat (M).tensor)) b).LaxBraided]
    (hl : ∀ a : C, SameLeftGather (Π) a L) (hr : ∀ b : C, SameRightGather R b)
    (hf : CircuitTrace M R L J p f) (hg : CircuitTrace M R L J q g) :
    CircuitTrace M R L J (p.tensor q) (independentNativeWordMap (Π) f g R L) where
  coefficient z := biTensorIso (T:=Π) (hf.coefficient z.1) (hg.coefficient z.2)
  trace := NativeAddressTrace.tensor R L hl hr hf.trace hg.trace
  values V z h := ⟨hf.values V z.1 h.1,hg.values V z.2 h.2⟩
  circuit_eval V z hz := by
    have es := (Tagging.matches_eval V mul a s z.1 hz.1).symm
    have et := (Tagging.matches_eval V mul c t z.2 hz.2).symm
    have ed := (Tagging.matches_eval V mul b p.target (p.read z.1) (hf.values V z.1 hz.1)).symm
    have ek := (Tagging.matches_eval V mul d q.target (q.read z.2) (hg.values V z.2 hz.2)).symm
    exact biMap_heq (T:=Π) es ed et ek (hf.circuit_eval V z.1 hz.1) (hg.circuit_eval V z.2 hz.2)

def TaggingTransport.reverse {a b : Tree} {s : Tagging Tag a} (p : TaggingTransport s b) :
    TaggingTransport p.target a :=
  ⟨s,.reverse p.circuit,p.read.symm⟩

set_option backward.isDefEq.respectTransparency false in
omit [MonoidalCategory C] [SymmetricCategory C] in
theorem iso_inv_heq {a b c d : C} (e : a = c) (f : b = d) {p : a ≅ b} {q : c ≅ d}
    (h : HEq p.hom q.hom) : HEq p.inv q.inv := by
  subst c; subst d
  have h' : p = q := Iso.ext (eq_of_heq h)
  subst q; rfl

set_option backward.isDefEq.respectTransparency false in
def CircuitTrace.reverse {a b : Tree} {s : Tagging Tag a} {p : TaggingTransport s b}
    (η : NativeAugmentedIso (separate R L J a) (separate R L J b))
    (hf : CircuitTrace M R L J p η.hom.native)
    (hv : ∀ (V : Tag → C) (z : b.Address), p.target.Matches (T:=Π) V z → s.Matches (T:=Π) V (p.read.symm z)) :
    CircuitTrace M R L J p.reverse η.inv.native where
  coefficient z := eqToIso (congrArg (lc b) (p.read.apply_symm_apply z).symm) ≪≫
    (hf.coefficient (p.read.symm z)).symm
  trace := NativeAddressTrace.reverse η hf.trace
  values := hv
  circuit_eval V z hz := by
    let e := p.read
    let x := e.symm z
    let k := congrArg (lc b) (e.apply_symm_apply z).symm
    have hx := hv V z hz
    have hy := hf.values V x hx
    have l : HEq (hf.coefficient x).inv (eval V p.circuit).inv :=
      iso_inv_heq (Tagging.matches_eval V mul a s x hx).symm
        (Tagging.matches_eval V mul b p.target (e x) hy).symm (hf.circuit_eval V x hx)
    change HEq (eqToHom k ≫ (hf.coefficient x).inv) (eval V p.circuit).inv
    exact (hom_source_pin_heq k ((hf.coefficient x).inv)).trans l

set_option backward.isDefEq.respectTransparency false in
theorem CircuitTrace.eq {a b : Tree} {s : Tagging Tag a}
    {p q : TaggingTransport s b}
    {f g : Hom (@standardPush C cat add sa) (separate R L J a).base (separate R L J b).base}
    (hf : CircuitTrace M R L J p f) (hg : CircuitTrace M R L J q g)
    (hn : s.expr.leaves.Nodup) (sameTags : p.target = q.target) (sameRead : p.read = q.read)
    (labels : ∀ z : a.Address, ∃ V : Tag → C, s.Matches (T:=Π) V z) : f = g := by
  obtain ⟨pT,pC,pR⟩ := p
  obtain ⟨qT,qC,qR⟩ := q
  change pT = qT at sameTags
  change pR = qR at sameRead
  subst qT; subst qR
  apply NativeAddressTrace.eq hf.trace hg.trace
  intro z
  obtain ⟨V,hV⟩ := labels z
  have E := @TensorCircuit.coherent C cat mul sm Tag V _ _ pC qC hn
  exact eq_of_heq ((hf.circuit_eval V z hV).trans ((heq_of_eq E).trans (hg.circuit_eval V z hV).symm))

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter.DependentFubiniTree
