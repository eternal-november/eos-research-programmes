module

public import WitnessedDecompositions.FreeExtension
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Semantic refinement categories

Actual occurrence-indexed tuples are arrows; equality of their substituted totals
is only endpoint evidence, never an equality relation on tuples. The target
calculus and all interfaces/components are arbitrary, including nullary profiles.
Contract v0.1 SHA256 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

universe u v w w' w''
namespace WitnessedDecompositions
open CategoryTheory
namespace Calc
variable {V : Type u} [Quiver.{v} V]

/-- Substitution commutes with component equality transport. -/
theorem subst_componentTransport (M : Calc.{u,v,w} V) {c d : Component V}
    (e : c = d) (a : M.Op c) (f : M.toCollection.Family (M.profile a)) :
    Path.occurrenceTransport M.Op e (M.subst a f) =
      M.subst (Path.occurrenceTransport M.Op e a)
        (Path.pathFamilyCast M.Op
          (M.toCollection.profile_occurrenceTransport e a).symm
          (Path.componentPathFamilyCast M.Op e (M.profile a) f)) := by
  cases e
  rfl

/-- Path-family reindexing is the canonical dependent occurrence transport. -/
theorem reindex_eq_pathFamilyCast (M : Calc.{u,v,w} V) {a b : V}
    {p q : Quiver.Path a b} (h : p = q) (f : M.toCollection.Family q) :
    M.toCollection.reindex h f = Path.pathFamilyCast M.Op h.symm f := by
  cases h
  rfl

/-- Component equality transports an identity without making any choices. -/
theorem identity_componentTransport (M : Calc.{u,v,w} V) {c d : Component V}
    (e : c = d) : Path.occurrenceTransport M.Op e (M.identity c) = M.identity d := by
  cases e
  rfl

/-- Restricting an identity family gives the identity at each actual occurrence. -/
theorem expandFamily_identity (M : Calc.{u,v,w} V) {a b : V}
    (p : Quiver.Path a b)
    (q : ∀ i : Path.Slot p,
      Quiver.Path (Path.componentAt p i).source (Path.componentAt p i).target)
    (i : Path.Slot p) :
    Path.expandFamily M.Op p q (M.identityFamily (Path.expand p q)) i =
      M.identityFamily (q i) := by
  funext j
  unfold Path.expandFamily CalcData.identityFamily
  exact M.identity_componentTransport _

/-- Identity forest on the right, as an equality of complete tuples. -/
theorem composeAt_identity (M : Calc.{u,v,w} V) {a b : V}
    {p : Quiver.Path a b} (f : M.toCollection.Family p) :
    M.composeAt f (M.identityFamily (M.toCollection.familyProfile f)) = f := by
  funext i
  exact (congrArg (M.subst (f i))
    (M.expandFamily_identity p (fun i => M.profile (f i)) i)).trans (M.subst_identity (f i))

/-- Identity forest on the left, including the empty profile. -/
theorem identity_composeAt (M : Calc.{u,v,w} V) {a b : V}
    (p : Quiver.Path a b) (f : M.toCollection.Family p) :
    M.composeAt (M.identityFamily p)
      (M.toCollection.reindex (M.identityFamily_profile p) f) = f := by
  let q := fun i : Path.Slot p => M.profile (M.identity (Path.componentAt p i))
  let q' := fun i : Path.Slot p => (Path.componentAt p i).edge.toPath
  have eqs : q = q' := by
    funext i
    exact M.profile_identity _
  let h := M.toCollection.reindex (Path.expand_edges p) f
  have castEq : M.toCollection.reindex (M.identityFamily_profile p) f =
      Path.pathFamilyCast M.Op (congrArg (Path.expand p) eqs).symm h := by
    rw [M.reindex_eq_pathFamilyCast]
    dsimp only [h]
    rw [M.reindex_eq_pathFamilyCast, Path.pathFamilyCast_trans]
  funext i
  change M.subst (M.identity (Path.componentAt p i))
    (Path.expandFamily M.Op p q _ i) = f i
  rw [castEq, Path.expandFamily_pathCast M.Op p q q' eqs]
  have inner : Path.expandFamily M.Op p q' h i = M.toCollection.singletonFamily (f i) := by
    funext j
    rcases j with j | ⟨⟩
    · exact nomatch j
    · rw [Path.expandFamily_edges]
      dsimp only [h]
      rw [M.reindex_eq_pathFamilyCast, Path.pathFamilyCast_trans]
      rfl
  rw [inner]
  exact M.identity_subst (f i)

/-- Associativity with the second family indexed by its independently expanded profile. -/
theorem subst_assocAt (M : Calc.{u,v,w} V) {c : Component V}
    (a : M.Op c) (f : M.toCollection.Family (M.profile a))
    (h : M.toCollection.Family (M.toCollection.familyProfile f)) :
    M.subst (M.subst a f) (M.toCollection.reindex (M.profile_subst a f) h) =
      M.subst a (M.composeAt f h) := by
  rw [M.subst_assoc]
  congr 1
  unfold CalcData.composeFamily CalcData.innerFamily CalcData.composeAt
  rw [Collection.reindex_comp]
  rfl

/-- Associativity of forest composition retains every original tuple entry.
Its proof uses full three-layer typed occurrence coherence, not cancellation
of an outer operation. -/
theorem composeAt_assoc (M : Calc.{u,v,w} V) {a b : V}
    {p : Quiver.Path a b} (f : M.toCollection.Family p)
    (h : M.toCollection.Family (M.toCollection.familyProfile f))
    (k : M.toCollection.Family (M.toCollection.familyProfile h)) :
    M.composeAt (M.composeAt f h)
      (M.toCollection.reindex (M.composeAt_profile f h).symm k) =
      M.composeAt f (M.composeAt h k) := by
  let q := fun i => M.profile (f i)
  let fi := Path.expandFamily M.Op p q h
  let r := fun j => M.profile (h j)
  let ri := Path.expandFamily (fun c => Quiver.Path c.source c.target) p q r
  have eri : (fun i j => M.profile (fi i j)) = ri := by
    funext i j
    exact M.toCollection.profile_expandFamily p q h i j
  let qq := fun i => M.profile (M.subst (f i) (fi i))
  let qq' := fun i => Path.expand (q i) (ri i)
  have eqs : qq = qq' := by
    funext i
    exact (M.profile_subst (f i) (fi i)).trans
      (congrArg (Path.expand (q i)) (congrFun eri i))
  let kk := Path.pathFamilyCast M.Op (Path.expand_assoc p q r) k
  have outerCast : M.toCollection.reindex (M.composeAt_profile f h).symm k =
      Path.pathFamilyCast M.Op (congrArg (Path.expand p) eqs).symm kk := by
    rw [reindex_eq_pathFamilyCast]
    dsimp only [kk]
    rw [Path.pathFamilyCast_trans]
  funext i
  change M.subst (M.subst (f i) (fi i))
    (Path.expandFamily M.Op p qq _ i) = _
  rw [outerCast, Path.expandFamily_pathCast M.Op p qq qq' eqs]
  let hhi := Path.expandFamily M.Op p qq' kk i
  let ki : M.toCollection.Family (M.toCollection.familyProfile (fi i)) :=
    Path.pathFamilyCast M.Op (congrArg (Path.expand (q i)) (congrFun eri i)).symm hhi
  have innerCast : Path.pathFamilyCast M.Op (congrFun eqs i).symm hhi =
      M.toCollection.reindex (M.profile_subst (f i) (fi i)) ki := by
    rw [reindex_eq_pathFamilyCast]
    dsimp only [ki]
    rw [Path.pathFamilyCast_trans]
  change M.subst (M.subst (f i) (fi i))
    (Path.pathFamilyCast M.Op (congrFun eqs i).symm hhi) = _
  rw [innerCast, M.subst_assocAt]
  congr 1
  funext j
  change M.subst (fi i j)
    (Path.expandFamily M.Op (q i) (fun j => M.profile (fi i j)) ki j) =
      Path.occurrenceTransport M.Op (Path.componentAt_slotExpand_symm p q ⟨i,j⟩)
        (M.subst (h ((Path.slotExpand p q).symm ⟨i,j⟩))
          (Path.expandFamily M.Op (Path.expand p q) r k
            ((Path.slotExpand p q).symm ⟨i,j⟩)))
  rw [M.subst_componentTransport]
  congr 1
  dsimp only [ki]
  rw [Path.expandFamily_pathCast M.Op (q i)
    (fun j => M.profile (fi i j)) (ri i) (congrFun eri i)]
  congr 1
  funext l
  exact Path.expandFamily_assoc M.Op p q r k i j l


/-- Strict morphisms commute with forest substitution, before choosing endpoints. -/
theorem Hom.map_composeAt {M : Calc.{u,v,w} V} {N : Calc.{u,v,w'} V}
    (H : Hom M N) {a b : V} {p : Quiver.Path a b}
    (f : M.toCollection.Family p)
    (g : M.toCollection.Family (M.toCollection.familyProfile f)) :
    H.toHom.onFamily (M.composeAt f g) =
      N.composeAt (H.toHom.onFamily f)
        (N.toCollection.reindex (H.toHom.familyProfile_onFamily f)
          (H.toHom.onFamily g)) := by
  let q := fun i => M.profile (f i)
  let q' := fun i => N.profile (H.map (f i))
  have eqs : q' = q := by
    funext i
    exact H.profile_map (f i)
  have castEq : N.toCollection.reindex (H.toHom.familyProfile_onFamily f)
        (H.toHom.onFamily g) =
      Path.pathFamilyCast N.Op (congrArg (Path.expand p) eqs).symm
        (H.toHom.onFamily g) := by
    rw [N.reindex_eq_pathFamilyCast]
  funext i
  change H.map (M.subst (f i) (Path.expandFamily M.Op p q g i)) = _
  rw [H.map_subst]
  change N.subst (H.map (f i)) _ = N.subst (H.map (f i))
    (Path.expandFamily N.Op p q' _ i)
  rw [castEq, Path.expandFamily_pathCast N.Op p q' q eqs]
  congr 1
  rw [N.reindex_eq_pathFamilyCast]
  congr 1
  funext j
  exact Path.expandFamily_natural M.Op N.Op (fun _ => H.map) p q g i j

end Calc

namespace RefinementForest
variable {V : Type u} [Quiver.{v} V] (M : Calc.{u,v,w} V)

/-- An occurrence-indexed forest with its exact concatenated target profile. -/
def Arrow {a b : V} (p q : Quiver.Path a b) :=
  { f : M.toCollection.Family p // M.toCollection.familyProfile f = q }

variable {M}
/-- One identity at every original occurrence. -/
def id {a b : V} (p : Quiver.Path a b) : Arrow M p p :=
  ⟨M.identityFamily p, M.identityFamily_profile p⟩

/-- Typed forest composition; the middle-profile equality only reindexes occurrences. -/
def comp {a b : V} {p q r : Quiver.Path a b}
    (f : Arrow M p q) (g : Arrow M q r) : Arrow M p r :=
  ⟨M.composeAt f.val (M.toCollection.reindex f.property g.val),
    (M.composeAt_profile f.val _).symm.trans
      ((M.toCollection.familyProfile_reindex f.property g.val).trans g.property)⟩

@[simp] theorem id_comp {a b : V} {p q : Quiver.Path a b}
    (f : Arrow M p q) : comp (id p) f = f := by
  apply Subtype.ext
  exact M.identity_composeAt p f.val

@[simp] theorem comp_id {a b : V} {p q : Quiver.Path a b}
    (f : Arrow M p q) : comp f (id q) = f := by
  rcases f with ⟨f,hf⟩
  subst q
  apply Subtype.ext
  exact M.composeAt_identity f

/-- Associativity is equality of forests, not merely equality of total profiles. -/
theorem assoc {a b : V} {p q r s : Quiver.Path a b}
    (f : Arrow M p q) (g : Arrow M q r) (h : Arrow M r s) :
    comp (comp f g) h = comp f (comp g h) := by
  rcases f with ⟨f,hf⟩
  subst q
  rcases g with ⟨g,hg⟩
  subst r
  apply Subtype.ext
  exact M.composeAt_assoc f g h.val


/-- Mapping a forest preserves its independently specified source and target paths. -/
def map {N : Calc.{u,v,w'} V} (H : Calc.Hom M N) {a b : V}
    {p q : Quiver.Path a b} (f : Arrow M p q) : Arrow N p q :=
  ⟨H.toHom.onFamily f.val, (H.toHom.familyProfile_onFamily f.val).trans f.property⟩

@[simp] theorem map_id {N : Calc.{u,v,w'} V} (H : Calc.Hom M N) {a b : V}
    (p : Quiver.Path a b) : map H (id p) = id p := by
  apply Subtype.ext
  funext i
  exact H.map_identity _

theorem map_comp {N : Calc.{u,v,w'} V} (H : Calc.Hom M N) {a b : V}
    {p q r : Quiver.Path a b} (f : Arrow M p q) (g : Arrow M q r) :
    map H (comp f g) = comp (map H f) (map H g) := by
  rcases f with ⟨f,hf⟩
  subst q
  apply Subtype.ext
  exact H.map_composeAt f g.val

/-- Equality transport of forest endpoints keeps all operation entries. -/
def cast {a b : V} {p p' q q' : Quiver.Path a b}
    (hp : p = p') (hq : q = q') (f : Arrow M p' q') : Arrow M p q := by
  cases hp
  cases hq
  exact f

@[simp] theorem cast_rfl {a b : V} {p q : Quiver.Path a b} (f : Arrow M p q) :
    cast rfl rfl f = f := rfl

@[simp] theorem cast_id {a b : V} {p q : Quiver.Path a b} (e : p = q) :
    cast e e (id q : Arrow M q q) = id p := by
  cases e
  rfl

theorem cast_comp {a b : V} {p p' q q' r r' : Quiver.Path a b}
    (hp : p = p') (hq : q = q') (hr : r = r')
    (f : Arrow M p' q') (g : Arrow M q' r') :
    cast hp hr (comp f g) = comp (cast hp hq f) (cast hq hr g) := by
  cases hp
  cases hq
  cases hr
  rfl

@[simp] theorem cast_val {a b : V} {p p' q q' : Quiver.Path a b}
    (hp : p = p') (hq : q = q') (f : Arrow M p' q') :
    (cast hp hq f).val = M.toCollection.reindex hp f.val := by
  cases hp
  cases hq
  rfl

end RefinementForest

namespace SemanticRefinement
variable {V : Type u} [Quiver.{v} V]

/-- Semantic refinement retains the entire tuple, including each entry's profile. -/
def Arrow (M : Calc.{u,v,w} V) {c : Component V} (a b : M.Op c) :=
  { f : M.toCollection.Family (M.profile a) // M.subst a f = b }

variable {M : Calc.{u,v,w} V} {c : Component V}

/-- The typed forest underlying an arrow is obtained without forgetting any data. -/
def toForest {a b : M.Op c} (f : Arrow M a b) :
    RefinementForest.Arrow M (M.profile a) (M.profile b) :=
  ⟨f.val, (M.profile_subst a f.val).symm.trans (congrArg M.profile f.property)⟩

theorem toForest_injective {a b : M.Op c} :
    Function.Injective (@toForest _ _ M c a b) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun z : RefinementForest.Arrow M (M.profile a) (M.profile b) => z.val) h

/-- The identity tuple, not just its total evaluated witness. -/
def id (a : M.Op c) : Arrow M a a :=
  ⟨M.identityFamily (M.profile a), M.subst_identity a⟩

/-- Substitute each second-layer block into its own first-layer entry. -/
def comp {a b d : M.Op c} (f : Arrow M a b) (g : Arrow M b d) : Arrow M a d :=
  ⟨(RefinementForest.comp (toForest f) (toForest g)).val, by
    rcases f with ⟨f,hf⟩
    cases hf
    exact (M.subst_assoc a f g.val).symm.trans g.property⟩

@[simp] theorem toForest_id (a : M.Op c) :
    toForest (id a) = RefinementForest.id (M.profile a) := rfl

@[simp] theorem toForest_comp {a b d : M.Op c} (f : Arrow M a b) (g : Arrow M b d) :
    toForest (comp f g) = RefinementForest.comp (toForest f) (toForest g) := rfl

@[simp] theorem id_comp {a b : M.Op c} (f : Arrow M a b) : comp (id a) f = f := by
  apply toForest_injective
  simp only [toForest_comp, toForest_id, RefinementForest.id_comp]

@[simp] theorem comp_id {a b : M.Op c} (f : Arrow M a b) : comp f (id b) = f := by
  apply toForest_injective
  simp only [toForest_comp, toForest_id, RefinementForest.comp_id]

theorem assoc {a b d e : M.Op c} (f : Arrow M a b) (g : Arrow M b d)
    (h : Arrow M d e) : comp (comp f g) h = comp f (comp g h) := by
  apply toForest_injective
  simp only [toForest_comp, RefinementForest.assoc]

/-- Wrapper avoids conflating the raw Tree category with its equivalent semantic copy. -/
structure Object (M : Calc.{u,v,w} V) (c : Component V) where
  val : M.Op c

instance : CategoryTheory.Category (Object M c) where
  Hom a b := Arrow M a.val b.val
  id a := id a.val
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc


/-- Every strict calculus map acts entrywise on retained arrow tuples. -/
def mapArrow {N : Calc.{u,v,w'} V} (H : Calc.Hom M N)
    {a b : M.Op c} (f : Arrow M a b) : Arrow N (H.map a) (H.map b) :=
  ⟨N.toCollection.reindex (H.profile_map a) (H.toHom.onFamily f.val),
    (H.map_subst a f.val).symm.trans (congrArg H.map f.property)⟩

theorem toForest_mapArrow {N : Calc.{u,v,w'} V} (H : Calc.Hom M N)
    {a b : M.Op c} (f : Arrow M a b) :
    toForest (mapArrow H f) =
      RefinementForest.cast (H.profile_map a) (H.profile_map b)
        (RefinementForest.map H (toForest f)) := by
  apply Subtype.ext
  rw [RefinementForest.cast_val]
  rfl

@[simp] theorem mapArrow_id {N : Calc.{u,v,w'} V} (H : Calc.Hom M N)
    (a : M.Op c) : mapArrow H (id a) = id (H.map a) := by
  apply toForest_injective
  rw [toForest_mapArrow, toForest_id, RefinementForest.map_id,
    RefinementForest.cast_id, toForest_id]

theorem mapArrow_comp {N : Calc.{u,v,w'} V} (H : Calc.Hom M N)
    {a b d : M.Op c} (f : Arrow M a b) (g : Arrow M b d) :
    mapArrow H (comp f g) = comp (mapArrow H f) (mapArrow H g) := by
  apply toForest_injective
  rw [toForest_mapArrow, toForest_comp, RefinementForest.map_comp,
    RefinementForest.cast_comp _ (H.profile_map b), toForest_comp,
    toForest_mapArrow, toForest_mapArrow]

/-- Interpretation induces an actual category-theoretic functor. -/
def functor {N : Calc.{u,v,w'} V} (H : Calc.Hom M N) (c : Component V) :
    Object M c ⥤ Object N c where
  obj a := ⟨H.map a.val⟩
  map := mapArrow H
  map_id a := mapArrow_id H a.val
  map_comp := mapArrow_comp H

@[simp] theorem mapArrow_identity {a b : M.Op c} (f : Arrow M a b) :
    mapArrow (Calc.Hom.id M) f = f := rfl

@[simp] theorem mapArrow_composite {N : Calc.{u,v,w'} V} {P : Calc.{u,v,w''} V}
    (H : Calc.Hom M N) (K : Calc.Hom N P) {a b : M.Op c}
    (f : Arrow M a b) : mapArrow (H.comp K) f = mapArrow K (mapArrow H f) := by
  apply Subtype.ext
  change P.toCollection.reindex ((H.comp K).profile_map a) (fun i => K.map (H.map (f.val i))) =
    P.toCollection.reindex (K.profile_map (H.map a)) (K.toHom.onFamily
      (N.toCollection.reindex (H.profile_map a) (H.toHom.onFamily f.val)))
  rw [Collection.Hom.onFamily_reindex, Collection.reindex_comp]
  rfl

/-- Componentwise operation injectivity reflects equality of whole arrow tuples. -/
theorem mapArrow_injective {N : Calc.{u,v,w'} V} (H : Calc.Hom M N)
    (hinj : ∀ d : Component V, Function.Injective (@H.map d))
    {a b : M.Op c} : Function.Injective (@mapArrow _ _ M c N H a b) := by
  intro f g h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  change N.toCollection.reindex (H.profile_map a) (H.toHom.onFamily f.val) =
    N.toCollection.reindex (H.profile_map a) (H.toHom.onFamily g.val) at hh
  have hfamily : H.toHom.onFamily f.val = H.toHom.onFamily g.val := by
    have := congrArg (N.toCollection.reindex (H.profile_map a).symm) hh
    simpa only [Collection.reindex_comp, Collection.reindex_refl] using this
  funext i
  exact hinj _ (congrFun hfamily i)

/-- Object recovery is a separate injectivity statement, not categorical faithfulness. -/
theorem reflects_object_equality {N : Calc.{u,v,w'} V} (H : Calc.Hom M N)
    (hinj : Function.Injective (@H.map c)) {a b : M.Op c}
    (h : H.map a = H.map b) : a = b := hinj h

end SemanticRefinement

end WitnessedDecompositions
