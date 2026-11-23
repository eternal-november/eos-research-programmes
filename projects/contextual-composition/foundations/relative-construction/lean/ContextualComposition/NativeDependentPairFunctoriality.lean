module
public import ContextualComposition.NativeDependentPairFinite
@[expose] public section

/-! Transport the checked native dependent functor laws to arbitrary
families using exact recovery of the original input arrows. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
local notation "ℙ" => standardPush (C:=C)

set_option backward.isDefEq.respectTransparency false in
theorem wordNativeMap_cells_ext {X Y : Type u} [DecidableEq Y]
    {xs : List X} {ys : List Y} {f : X → Y} (hs : ∀ x ∈ xs, f x ∈ ys) (ht : ys.Nodup)
    (A : X → C) (B : Y → C)
    (p q : ∀ y ∈ ys, fold 𝒮 Zₐ A (wordFibre xs f y) ⟶ B y)
    (h : wordNativeMap f hs ht A B (fun j => p ys[j] (List.getElem_mem _)) =
      wordNativeMap f hs ht A B (fun j => q ys[j] (List.getElem_mem _))) :
    p = q := by
  have k := eq_of_heq (Hom.mk.inj h).2
  funext y hy
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hy
  let j : Fin ys.length := ⟨i,hi⟩
  have he := congrFun k j
  exact (cancel_epi (eqToHom (wordCarrier_fibre_pin f hs ht A j))).mp he

set_option backward.isDefEq.respectTransparency false in
theorem OrderedDependentMap.ext_of_native {X U Y V : Type u} [DecidableEq Y] [DecidableEq V]
    {xs : List X} {us : X → List U} {ys : List Y} {vs : Y → List V}
    {A : X → C} {B : X → U → C} {D : Y → C} {E : Y → V → C}
    (p q : OrderedDependentMap xs us ys vs A B D E)
    (hy : ys.Nodup) (hv : ∀ y ∈ ys, (vs y).Nodup)
    (hp : p.parent = q.parent) (hc : p.child = q.child)
    (h₀ : p.outerNative hy = q.outerNative hy)
    (h₁ : ∀ x hx, HEq (p.innerNative x hx (hv _ (p.parent_mem x hx)))
      (q.innerNative x hx (hv _ (q.parent_mem x hx)))) :
    p = q := by
  cases p with | mk p₀ p₁ ph₀ ph₁ c₀ c₁ =>
    cases q with | mk q₀ q₁ qh₀ qh₁ d₀ d₁ =>
      dsimp only at hp hc
      subst q₀
      subst q₁
      have ho : c₀ = d₀ := wordNativeMap_cells_ext ph₀ hy A D c₀ d₀ h₀
      have hi : c₁ = d₁ := by
        funext x hx
        exact wordNativeMap_cells_ext (ph₁ x hx) (hv _ (ph₀ x hx)) _ _ _ _ (eq_of_heq (h₁ x hx))
      subst d₀
      subst d₁
      rfl

namespace NativeDependentPairHom
variable {I : C} {A B D : NativeDependentPair I}

noncomputable def ident (A : NativeDependentPair I) : NativeDependentPairHom A A where
  parent := AugHom.ident A.parent
  child x := AugHom.ident (A.child x)

noncomputable def comp (p : NativeDependentPairHom A B) (q : NativeDependentPairHom B D) : NativeDependentPairHom A D where
  parent := p.parent.comp q.parent
  child x := (p.child x).comp (q.child (p.parent.native.addr x))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem ordered_identity (A : NativeDependentPair I) :
    letI := A.ordered.eqX
    letI := A.ordered.eqU
    (ident A).ordered.map = OrderedDependentMap.identity A.ordered.xs A.ordered.us A.ordered.V A.ordered.A
      A.ordered.xs_unique A.ordered.us_unique := by
  letI := A.ordered.eqX
  letI := A.ordered.eqU
  let B := A.ordered
  let p := ident A
  let q := OrderedDependentMap.identity B.xs B.us B.V B.A B.xs_unique B.us_unique
  have hid {F G : Family C} (e : F = G) : HEq (Hom.ident (S:=ℙ) F) (Hom.ident (S:=ℙ) G) := by subst G; rfl
  refine OrderedDependentMap.ext_of_native p.ordered.map q B.xs_unique B.us_unique rfl ?_ ?_ ?_
  · funext x a
    rcases a with ⟨a⟩
    cases a with
    | none => rfl
    | some z => cases z; rfl
  · have e := OrderedDependentMap.identity_outer A.ordered.xs A.ordered.us A.ordered.V A.ordered.A
      A.ordered.xs_unique A.ordered.us_unique
    change q.outerNative B.xs_unique = Hom.ident _ at e
    rw [e]
    exact eq_of_heq ((p.outer_recovers).trans (hid A.parentView.family_eq).symm)
  · intro x hx
    have e := OrderedDependentMap.identity_inner A.ordered.xs A.ordered.us A.ordered.V A.ordered.A
      A.ordered.xs_unique A.ordered.us_unique x hx
    change q.innerNative x hx _ = Hom.ident _ at e
    rw [e]
    exact (p.inner_recovers x hx).trans (hid (A.childView x.down).family_eq).symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem ordered_comp (p : NativeDependentPairHom A B) (q : NativeDependentPairHom B D) :
    letI := B.ordered.eqX
    letI := B.ordered.eqU
    letI := D.ordered.eqX
    letI := D.ordered.eqU
    (p.comp q).ordered.map = p.ordered.map.compose q.ordered.map B.ordered.xs_unique D.ordered.xs_unique
      (fun x hx => B.ordered.us_unique _ (p.ordered.map.parent_mem x hx))
      (fun y hy => D.ordered.us_unique _ (q.ordered.map.parent_mem y hy)) := by
  letI := B.ordered.eqX
  letI := B.ordered.eqU
  letI := D.ordered.eqX
  letI := D.ordered.eqU
  let f := p.ordered.map
  let g := q.ordered.map
  let hb := fun x hx => B.ordered.us_unique _ (f.parent_mem x hx)
  let hd := fun y hy => D.ordered.us_unique _ (g.parent_mem y hy)
  let c := f.compose g B.ordered.xs_unique D.ordered.xs_unique hb hd
  refine OrderedDependentMap.ext_of_native (p.comp q).ordered.map c D.ordered.xs_unique D.ordered.us_unique rfl ?_ ?_ ?_
  · funext x a
    rcases a with ⟨a⟩
    cases a with
    | none => rfl
    | some z => cases z; rfl
  · have e := f.compose_outer g B.ordered.xs_unique D.ordered.xs_unique hb hd
    change c.outerNative _ = _ at e
    rw [e]
    exact eq_of_heq ((p.comp q).outer_recovers.trans
      (nativeHom_comp_heq (f.outerNative _) (g.outerNative _) p.parent.native q.parent.native
        A.parentView.family_eq B.parentView.family_eq D.parentView.family_eq p.outer_recovers q.outer_recovers).symm)
  · intro x hx
    have e := f.compose_inner g B.ordered.xs_unique D.ordered.xs_unique hb hd x hx
    change c.innerNative x hx _ = _ at e
    rw [e]
    let y := f.parent x
    let hy := f.parent_mem x hx
    exact ((p.comp q).inner_recovers x hx).trans
      (nativeHom_comp_heq (f.innerNative x hx _) (g.innerNative y hy _) (p.child x.down).native (q.child y.down).native
        (A.childView x.down).family_eq (B.childView y.down).family_eq (D.childView (g.parent y).down).family_eq
        (p.inner_recovers x hx) (q.inner_recovers y hy)).symm

variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ c : C, (leftFactor T c).LaxBraided] [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided]
variable (hl : ∀ c : C, SameLeftGather T c L) (hr : ∀ c : C, SameRightGather R c)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
include hr in
theorem accumulate_ident (A : NativeDependentPair I) :
    (ident A).accumulate R L J N NL hl = AugHom.ident (A.accumulate R L J) := by
  letI := A.ordered.eqX
  letI := A.ordered.eqU
  apply AugHom.ext
  change origDependentWordMap (ident A).ordered.map R L (dependentWord_nodup A.ordered.xs_unique A.ordered.us_unique) =
    Hom.ident _
  rw [ordered_identity A]
  exact origDependentWordMap_ident A.ordered.xs A.ordered.us A.ordered.V A.ordered.A
    A.ordered.xs_unique A.ordered.us_unique R L hl hr

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
include NR hr in
theorem accumulate_comp (p : NativeDependentPairHom A B) (q : NativeDependentPairHom B D) :
    (p.comp q).accumulate R L J N NL hl =
      (p.accumulate R L J N NL hl).comp (q.accumulate R L J N NL hl) := by
  letI := A.ordered.eqX
  letI := B.ordered.eqX
  letI := B.ordered.eqU
  letI := D.ordered.eqX
  letI := D.ordered.eqU
  let hb := dependentWord_nodup B.ordered.xs_unique B.ordered.us_unique
  let hd := dependentWord_nodup D.ordered.xs_unique D.ordered.us_unique
  let f := p.ordered.map
  let g := q.ordered.map
  apply AugHom.ext
  change origDependentWordMap (p.comp q).ordered.map R L hd =
    (origDependentWordMap f R L hb).comp (origDependentWordMap g R L hd)
  rw [ordered_comp p q]
  exact origDependentWordMap_comp f g B.ordered.xs_unique D.ordered.xs_unique
    (fun x hx => B.ordered.us_unique _ (f.parent_mem x hx))
    (fun y hy => D.ordered.us_unique _ (g.parent_mem y hy))
    R L A.ordered.xs_unique A.ordered.us_unique hb hd N NR NL hl hr

set_option backward.isDefEq.respectTransparency false in
theorem ext_native {p q : NativeDependentPairHom A B}
    (e : p.parent = q.parent) (h : ∀ x, HEq (p.child x) (q.child x)) : p = q := by
  cases p with | mk p₀ p₁ =>
    cases q with | mk q₀ q₁ =>
      dsimp only at e
      subst q₀
      exact congrArg (NativeDependentPairHom.mk p₀) (funext fun x => eq_of_heq (h x))

end NativeDependentPairHom
noncomputable instance {I : C} : Category (Aug (standardPush (C:=C)) I) where
  Hom A B := AugHom ℙ A B
  id := AugHom.ident
  comp := AugHom.comp
  id_comp := AugHom.ident_comp
  comp_id := AugHom.comp_ident
  assoc := AugHom.comp_assoc

noncomputable instance {I : C} : Category (NativeDependentPair I) where
  Hom := NativeDependentPairHom
  id := NativeDependentPairHom.ident
  comp := NativeDependentPairHom.comp
  id_comp p := NativeDependentPairHom.ext_native (AugHom.ident_comp p.parent)
    (fun x => heq_of_eq (AugHom.ident_comp (p.child x)))
  comp_id p := NativeDependentPairHom.ext_native (AugHom.comp_ident p.parent)
    (fun x => heq_of_eq (AugHom.comp_ident (p.child x)))
  assoc p q r := NativeDependentPairHom.ext_native (AugHom.comp_assoc p.parent q.parent r.parent)
    (fun x => heq_of_eq (AugHom.comp_assoc (p.child x)
      (q.child (p.parent.native.addr x)) (r.child (q.parent.native.addr (p.parent.native.addr x)))))

variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (J : UnitCompat R I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ c : C, (leftFactor T c).LaxBraided] [rF : ∀ c : C, (rightFactor (T:=T) c).LaxBraided]
variable (hl : ∀ c : C, SameLeftGather T c L) (hr : ∀ c : C, SameRightGather R c)

set_option backward.isDefEq.respectTransparency false in
noncomputable def nativeAccumulationFunctor : NativeDependentPair I ⥤ Aug (standardPush (C:=C)) I where
  obj A := A.accumulate R L J
  map p := NativeDependentPairHom.accumulate R L J N NL hl p
  map_id A := NativeDependentPairHom.accumulate_ident R L J N NL hl hr A
  map_comp p q := NativeDependentPairHom.accumulate_comp R L J N NR NL hl hr p q

end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
