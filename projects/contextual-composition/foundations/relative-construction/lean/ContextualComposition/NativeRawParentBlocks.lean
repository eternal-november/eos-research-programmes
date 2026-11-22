module
public import ContextualComposition.NativeChildRegrouping
@[expose] public section
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
universe u

/-- The literal carrier obtained by two word maps reads as raw tag
composition; neither map has to be injective. -/
theorem wordCarrier_comp {X Y Z : Type u} {xs : List X} {ys : List Y} {zs : List Z}
    (f : X → Y) (g : Y → Z) (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
    (hy : ys.Nodup) (hz : zs.Nodup) :
    wordCarrier g hg hz ∘ wordCarrier f hf hy =
      wordCarrier (g ∘ f) (fun x hx => hg (f x) (hf x hx)) hz := by
  funext i
  apply Fin.ext
  apply hz.getElem_inj.mp
  change zs[wordCarrier g hg hz (wordCarrier f hf hy i)] =
    zs[wordCarrier (g ∘ f) (fun x hx => hg (f x) (hf x hx)) hz i]
  rw [wordCarrier_get, wordCarrier_get, wordCarrier_get]
  rfl

theorem wordCarrier_block_fibre {X Y Z : Type u} [DecidableEq Z]
    {xs : List X} {ys : List Y} {zs : List Z}
    (f : X → Y) (g : Y → Z) (hf : ∀ x ∈ xs, f x ∈ ys) (hg : ∀ y ∈ ys, g y ∈ zs)
    (hy : ys.Nodup) (hz : zs.Nodup) (z : Fin zs.length) :
    (fibreList (wordCarrier g hg hz ∘ wordCarrier f hf hy) z).map (fun i => xs[i]) =
      wordFibre xs (g ∘ f) zs[z] := by
  rw [wordCarrier_comp]
  exact wordCarrier_fibre (g ∘ f) (fun x hx => hg (f x) (hf x hx)) hz z

private theorem filter_true_pin {A : Type u} (xs : List A) : xs.filter (fun _ => true) = xs :=
  List.filter_eq_self.mpr (fun _ _ => rfl)

section ParentSelectors
variable {X U Y W X' Y' : Type u} [DecidableEq X'] [DecidableEq Y']
variable (xs : List X) (ys : List Y) (us : X → List U) (vs : Y → List W)
variable (f : X → X') (h : Y → Y')
variable (t : X' × Y')

theorem raw_parent_block_occurrence :
    wordFibre (fourOccurrenceExpr xs ys us vs).leaves
      (fun p : X × U × Y × W => (f p.1, h p.2.2.1)) t =
    (fourOccurrenceExpr (parentFibreA xs f t.1) (parentFibreB ys h t.2) us vs).leaves := by
  simp only [wordFibre, leaves_fourOccurrence, List.filter_flatMap, parentFibreA, parentFibreB,
    flatMap_filter_if]
  congr 1
  funext x
  by_cases hx : f x = t.1
  · simp only [hx, decide_true, ite_true]
    congr 1
    funext y
    congr 1
    funext z
    rw [List.filter_map]
    by_cases hz : h z = t.2 <;> simp [Function.comp_def, Prod.ext_iff, hx, hz, filter_true_pin]
  · simp [hx, List.filter_map, Function.comp_def, Prod.ext_iff]

theorem raw_parent_block_joint :
    wordFibre (fourJointExpr xs ys us vs).leaves
      (fun p : X × U × Y × W => (f p.1, h p.2.2.1)) t =
    (fourJointExpr (parentFibreA xs f t.1) (parentFibreB ys h t.2) us vs).leaves := by
  simp only [wordFibre, leaves_fourJoint, List.filter_flatMap, parentFibreA, parentFibreB,
    flatMap_filter_if]
  congr 1
  funext x
  by_cases hx : f x = t.1
  · simp only [hx, decide_true, ite_true]
    congr 1
    funext z
    by_cases hz : h z = t.2 <;>
      simp [hz, List.filter_map, Function.comp_def, Prod.ext_iff, hx, filter_true_pin]
  · simp [hx, List.filter_map, Function.comp_def, Prod.ext_iff]

end ParentSelectors
section LiteralSeparate
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
universe v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X U Y W X' U' Y' W' : Type u}
variable [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))

abbrev parentTag (t : X × U × Y × W) : X × Y := (t.1,t.2.2.1)
abbrev parentTagWord (xs : List X) (ys : List Y) := xs.flatMap (fun x => ys.map (fun y => (x,y)))

omit [DecidableEq X'] [DecidableEq U'] [DecidableEq Y'] [DecidableEq W'] in
theorem separate_parent_support : ∀ t ∈ (fourOccurrenceExpr xs' ys' us' vs').leaves,
    parentTag t ∈ parentTagWord xs' ys' := by
  intro t ht
  have m := (mem_fourOccurrence xs' ys' us' vs' t).mp ht
  exact List.mem_flatMap.mpr ⟨t.1, m.1, List.mem_map.mpr ⟨t.2.2.1, m.2.2.1, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The stable source word of a block of the actual independent-then-dependent
native map is the source occurrence word restricted only by the two
outer parent carriers. No child maps or multiplicities are discarded. -/
theorem separate_native_parent_source_word
    (hy : (fourOccurrenceExpr xs' ys' us' vs').leaves.Nodup)
    (hz : (parentTagWord xs' ys').Nodup) (z : Fin (parentTagWord xs' ys').length) :
    let sel := wordCarrier parentTag (separate_parent_support (us':=us') (vs':=vs')) hz
    let arc := separateBinaryMap D E R L hy
    let k := (parentTagWord xs' ys')[z]
    (fibreList (sel ∘ arc.addr) z).map (fun i => (fourOccurrenceExpr xs ys us vs).leaves[i]) =
      (fourOccurrenceExpr (parentFibreA xs D.parent k.1) (parentFibreB ys E.parent k.2) us vs).leaves := by
  intro sel arc k
  exact (wordCarrier_block_fibre (quadCarrierMap D.parent D.child E.parent E.child) parentTag
    (separateSupport D E) (separate_parent_support (us':=us') (vs':=vs')) hy hz z).trans
    (raw_parent_block_occurrence xs ys us vs D.parent E.parent k)

omit [DecidableEq U'] [DecidableEq W'] in
set_option backward.isDefEq.respectTransparency false in
theorem separate_native_parent_target_word
    (hz : (parentTagWord xs' ys').Nodup) (z : Fin (parentTagWord xs' ys').length) :
    let sel := wordCarrier parentTag (separate_parent_support (us':=us') (vs':=vs')) hz
    let k := (parentTagWord xs' ys')[z]
    (fibreList sel z).map (fun i => (fourOccurrenceExpr xs' ys' us' vs').leaves[i]) =
      (fourOccurrenceExpr (parentFibreA xs' id k.1) (parentFibreB ys' id k.2) us' vs').leaves := by
  intro sel k
  exact (wordCarrier_fibre parentTag (separate_parent_support (us':=us') (vs':=vs')) hz z).trans
    (raw_parent_block_occurrence xs' ys' us' vs' id id k)

end LiteralSeparate
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
