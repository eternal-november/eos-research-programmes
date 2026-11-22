module
public import ContextualComposition.BinaryCarrierWords

@[expose] public section
/-! Native binary variation in fixed ordered presentations. The side arrows
are built from the actual opaque parent and continuation maps, not from
the desired equality. Multiplicative and additive structures stay separate. -/
namespace ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
open CategoryTheory MonoidalCategory ContextualComposition.RigGrid
open scoped MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "𝒮" => binary (Additive.sum (Additive.ofBraided (C:=C)))
local notation "Zₐ" => 𝟙_ C
variable {X U X' U' : Type u} [DecidableEq X'] [DecidableEq U']

/-- Whole parent and continuation coefficient maps. A continuation map
is demanded only at valid source parents and valid target children. -/
structure OrderedDependentMap
    (xs : List X) (us : X → List U) (xs' : List X') (us' : X' → List U')
    (V : X → C) (W : X → U → C) (V' : X' → C) (W' : X' → U' → C) where
  parent : X → X'
  child : X → U → U'
  parent_mem : ∀ x ∈ xs, parent x ∈ xs'
  child_mem : ∀ x ∈ xs, ∀ u ∈ us x, child x u ∈ us' (parent x)
  outer : ∀ j ∈ xs',
    fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) V (parentFibreA xs parent j) ⟶ V' j
  inner : ∀ x ∈ xs, ∀ t ∈ us' (parent x),
    fold (binary (Additive.ofBraided (C:=C)).sum) (𝟙_ C) (W x) (childFibreA us child t x) ⟶ W' (parent x) t

namespace OrderedDependentMap
variable {xs : List X} {us : X → List U} {xs' : List X'} {us' : X' → List U'}
variable {V : X → C} {W : X → U → C} {V' : X' → C} {W' : X' → U' → C}
variable (D : OrderedDependentMap xs us xs' us' V W V' W')
abbrev Slice (j : X') := ParentSlice xs D.parent j
abbrev slice (j : X') := sliceWord xs D.parent j
abbrev terms (j : X') (t : U') : D.Slice j → List U := childFibreA us D.child t ∘ Subtype.val
abbrev parentVal (j : X') (x : D.Slice j) := V x.val
abbrev childVal (j : X') (x : D.Slice j) := W x.val

def locOuter (j : X') (hj : j ∈ xs') :
    fold 𝒮 Zₐ (D.parentVal j) (D.slice j) ⟶ V' j :=
  eqToHom ((std_fold_map V Subtype.val (D.slice j)).symm.trans
    (congrArg (fold 𝒮 Zₐ V) (sliceWord_map xs D.parent j))) ≫ D.outer j hj

def locInner (j : X') (t : U') (ht : t ∈ us' j) (x : D.Slice j) :
    DependentFibre.inner (S:=𝒮) (Z:=Zₐ) (indexInput (D.childVal j) (D.terms j t)) x ⟶ W' j t :=
  eqToHom (std_fold_map id (W x.val) (D.terms j t x)) ≫
    D.inner x.val x.property.1 t (x.property.2.symm ▸ ht) ≫
      eqToHom (congrArg (fun a => W' a t) x.property.2)

end OrderedDependentMap

section Binary
variable {Y W Y' W' : Type u} [DecidableEq Y'] [DecidableEq W']
variable {xs : List X} {ys : List Y} {us : X → List U} {vs : Y → List W}
variable {xs' : List X'} {ys' : List Y'} {us' : X' → List U'} {vs' : Y' → List W'}
variable {V : X → C} {P : Y → C} {A : X → U → C} {B : Y → W → C}
variable {V' : X' → C} {P' : Y' → C} {A' : X' → U' → C} {B' : Y' → W' → C}
variable (D : OrderedDependentMap xs us xs' us' V A V' A')
variable (E : OrderedDependentMap ys vs ys' vs' P B P' B')
variable {T : Bi (coeff (C:=C))}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (N : GridBinary (symmetricCross (C:=C)) R L)
variable (NR : GatherOuterNat R) (NL : GatherLeftNat L)

local notation "origS" => fourOccurrenceExpr xs ys us vs
local notation "origJ" => fourJointExpr xs ys us vs
local notation "nextS" => fourOccurrenceExpr xs' ys' us' vs'
local notation "nextJ" => fourJointExpr xs' ys' us' vs'
local notation "ps" => gridOrder (fourExchangeChart xs ys us vs)
local notation "pt" => gridOrder (fourExchangeChart xs' ys' us' vs')
local notation "srcS" => separateLeafLabels (T:=T) V P A B
local notation "srcJ" => jointLeafLabels (T:=T) V P A B
local notation "dstS" => separateLeafLabels (T:=T) V' P' A' B'
local notation "dstJ" => jointLeafLabels (T:=T) V' P' A' B'
set_option quotPrecheck false in
local notation "fm" => quadCarrierMap D.parent D.child E.parent E.child
local notation "ℙ" => standardPush (C:=C)

theorem separateSupport : ∀ t ∈ (origS).leaves, fm t ∈ (nextS).leaves :=
  quadCarrier_support xs ys us vs D.parent D.child E.parent E.child
    D.parent_mem D.child_mem E.parent_mem E.child_mem

theorem jointSupport : ∀ t ∈ (origJ).leaves, fm t ∈ (nextJ).leaves := by
  intro t ht
  exact (pt).perm.mem_iff.mp (separateSupport D E t ((ps).perm.mem_iff.mpr ht))

variable (t : X' × U' × Y' × W')
set_option quotPrecheck false in
local notation "lx" => D.slice t.1
set_option quotPrecheck false in
local notation "ly" => E.slice t.2.2.1
set_option quotPrecheck false in
local notation "lu" => D.terms t.1 t.2.1
set_option quotPrecheck false in
local notation "lv" => E.terms t.2.2.1 t.2.2.2
local notation "localS" => fourOccurrenceExpr lx ly lu lv
local notation "localJ" => fourJointExpr lx ly lu lv

def sliceRelabel (p : D.Slice t.1 × U × E.Slice t.2.2.1 × W) : X × U × Y × W :=
  quadOuterRelabel Subtype.val Subtype.val p

theorem local_separate_word :
    (localS).leaves.map (sliceRelabel D E t) = wordFibre (origS).leaves fm t := by
  have G := leaves_occurrence_relabel (fun x : D.Slice t.1 => x.val) (fun y : E.Slice t.2.2.1 => y.val)
    lx ly (childFibreA us D.child t.2.1) (childFibreB vs E.child t.2.2.2)
  change _ = _ at G
  calc
    _ = (fourOccurrenceExpr ((lx).map Subtype.val) ((ly).map Subtype.val)
      (childFibreA us D.child t.2.1) (childFibreB vs E.child t.2.2.2)).leaves := G
    _ = _ := by
      rw [sliceWord_map, sliceWord_map]
      exact (fibre_leaves_fourOccurrence xs ys us vs D.parent D.child E.parent E.child t).symm

theorem local_joint_word :
    (localJ).leaves.map (sliceRelabel D E t) = wordFibre (origJ).leaves fm t := by
  have G := leaves_joint_relabel (fun x : D.Slice t.1 => x.val) (fun y : E.Slice t.2.2.1 => y.val)
    lx ly (childFibreA us D.child t.2.1) (childFibreB vs E.child t.2.2.2)
  calc
    _ = (fourJointExpr ((lx).map Subtype.val) ((ly).map Subtype.val)
      (childFibreA us D.child t.2.1) (childFibreB vs E.child t.2.2.2)).leaves := G
    _ = _ := by
      rw [sliceWord_map, sliceWord_map]
      exact (fibre_leaves_fourJoint xs ys us vs D.parent D.child E.parent E.child t).symm

def separateBinaryCell (ht : t ∈ (nextS).leaves) :
    fold 𝒮 Zₐ srcS (wordFibre (origS).leaves fm t) ⟶ dstS t :=
  let p := (mem_fourOccurrence xs' ys' us' vs' t).mp ht
  localCellToGlobal srcS (sliceRelabel D E t) (local_separate_word D E t)
    (separateWordCell (D.slice t.1) (E.slice t.2.2.1) (D.terms t.1 t.2.1) (E.terms t.2.2.1 t.2.2.2) (D.parentVal t.1) (E.parentVal t.2.2.1)
      (D.childVal t.1) (E.childVal t.2.2.1) R L
      (D.locInner t.1 t.2.1 p.2.1) (E.locInner t.2.2.1 t.2.2.2 p.2.2.2)
      (D.locOuter t.1 p.1) (E.locOuter t.2.2.1 p.2.2.1))

def jointBinaryCell (ht : t ∈ (nextJ).leaves) :
    fold 𝒮 Zₐ srcJ (wordFibre (origJ).leaves fm t) ⟶ dstJ t :=
  let p := (mem_fourJoint xs' ys' us' vs' t).mp ht
  localCellToGlobal srcJ (sliceRelabel D E t) (local_joint_word D E t)
    (jointWordCell (D.slice t.1) (E.slice t.2.2.1) (D.terms t.1 t.2.1) (E.terms t.2.2.1 t.2.2.2) (D.parentVal t.1) (E.parentVal t.2.2.1)
      (D.childVal t.1) (E.childVal t.2.2.1) R L
      (D.locInner t.1 t.2.1 p.2.1) (E.locInner t.2.2.1 t.2.2.2 p.2.2.2)
      (D.locOuter t.1 p.1) (E.locOuter t.2.2.1 p.2.2.1))

noncomputable def separateBinaryMap (hy : (nextS).leaves.Nodup) :
    Hom ℙ (wordFamily srcS (origS).leaves) (wordFamily dstS (nextS).leaves) :=
  wordNativeMap fm (separateSupport D E) hy srcS dstS
    (fun j => separateBinaryCell D E R L (nextS).leaves[j] (List.getElem_mem _))

noncomputable def jointBinaryMap (hy : (nextS).leaves.Nodup) :
    Hom ℙ (wordFamily srcJ (origJ).leaves) (wordFamily dstJ (nextJ).leaves) :=
  wordNativeMap fm (jointSupport D E) ((pt).perm.nodup hy) srcJ dstJ
    (fun j => jointBinaryCell D E R L (nextJ).leaves[j] (List.getElem_mem _))


variable {I : C} (m : Middle T I)
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
include N NR NL in
/-- Naturality of the binary comparison on actual carrier-changing native
arrows assembled from opaque parent and continuation whole-fibre maps.
The assertion is a square of native `Hom`s between fixed ordered
presentations; it does not assert preservation of composition by the
horizontal constructions as functors. -/
theorem actual_binary_native_square (mi : MiddleInv m)
    (hx : (origS).leaves.Nodup) (hy : (nextS).leaves.Nodup)
    (h : MedialLinear m R L) (j : MedialInner m R L) :
    (separateBinaryMap D E R L hy).comp
        (nativeReindex (A:=wordFamily dstS (nextS).leaves) (B:=wordFamily dstJ (nextJ).leaves) (wordEquiv (pt).perm hy)
          (wordComparisonCells dstS dstJ pt hy (binaryLeafIso V' P' A' B' m mi))) =
    (nativeReindex (A:=wordFamily srcS (origS).leaves) (B:=wordFamily srcJ (origJ).leaves) (wordEquiv (ps).perm hx)
        (wordComparisonCells srcS srcJ ps hx (binaryLeafIso V P A B m mi))).comp
      (jointBinaryMap D E R L hy) := by
  apply (wordNativeMap_square_iff srcS srcJ dstS dstJ ps pt hx hy (separateSupport D E)
    (jointSupport D E) (binaryLeafIso V P A B m mi) (binaryLeafIso V' P' A' B' m mi)
    (fun t ht => separateBinaryCell D E R L t ht) (fun t ht => jointBinaryCell D E R L t ht)).mpr
  intro j'
  let t := (nextJ).leaves[j']
  let pt' : t ∈ (nextJ).leaves := List.getElem_mem _
  let ps' : t ∈ (nextS).leaves := (pt).perm.mem_iff.mpr pt'
  let ht := (mem_fourOccurrence xs' ys' us' vs' t).mp ps'
  exact (local_cell_square srcS srcJ (sliceRelabel D E t)
    (gridOrder (fourExchangeChart (D.slice t.1) (E.slice t.2.2.1) (D.terms t.1 t.2.1) (E.terms t.2.2.1 t.2.2.2))) (wordFibreOrder fm ps t)
    (local_separate_word D E t) (local_joint_word D E t) (hx.filter _)
    (fun k => (binaryLeafIso V P A B m mi k).hom)
    (separateWordCell (D.slice t.1) (E.slice t.2.2.1) (D.terms t.1 t.2.1) (E.terms t.2.2.1 t.2.2.2) (D.parentVal t.1) (E.parentVal t.2.2.1)
      (D.childVal t.1) (E.childVal t.2.2.1) R L
      (D.locInner t.1 t.2.1 ht.2.1) (E.locInner t.2.2.1 t.2.2.2 ht.2.2.2)
      (D.locOuter t.1 ht.1) (E.locOuter t.2.2.1 ht.2.2.1))
    (jointWordCell (D.slice t.1) (E.slice t.2.2.1) (D.terms t.1 t.2.1) (E.terms t.2.2.1 t.2.2.2) (D.parentVal t.1) (E.parentVal t.2.2.1)
      (D.childVal t.1) (E.childVal t.2.2.1) R L
      (D.locInner t.1 t.2.1 ht.2.1) (E.locInner t.2.2.1 t.2.2.2 ht.2.2.2)
      (D.locOuter t.1 ht.1) (E.locOuter t.2.2.1 ht.2.2.1))
    ((binaryLeafIso V' P' A' B' m mi t).hom)
    (binary_word_cell_square (D.slice t.1) (E.slice t.2.2.1) (D.terms t.1 t.2.1) (E.terms t.2.2.1 t.2.2.2) (D.parentVal t.1) (E.parentVal t.2.2.1)
      (D.childVal t.1) (E.childVal t.2.2.1) R L N NR NL m
      (D.locInner t.1 t.2.1 ht.2.1) (E.locInner t.2.2.1 t.2.2.2 ht.2.2.2)
      (D.locOuter t.1 ht.1) (E.locOuter t.2.2.1 ht.2.2.1) mi h j)).symm

end Binary
end ContextualComposition.NativeFinitePush.DependentFibre.RigGridNativeAdapter
