module
public import WitnessedDecompositions.Dynamic.Graph
public import WitnessedDecompositions.Dynamic.Occurrences
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u v w
namespace WitnessedDecompositions.Dynamic
open Path
namespace Assignment
variable {V : Type u} [Quiver.{v} V] (D : Assignment.{u,v,w} V)

/-- Unconstrained coordinate data. Boundary compatibility is imposed in `Op`. -/
structure MapOp (c : Component V) where
  profile : Quiver.Path c.source c.target
  maps : D.Family (D.component c) profile

namespace MapOp
variable {D}

def word {c : Component V} (a : D.MapOp c) :=
  Dynamic.word (fun d => Graph.Hom (D.component c) (D.component d)) a.profile a.maps

theorem ext_word {c : Component V} {a b : D.MapOp c}
    (hp : a.profile = b.profile) (hw : a.word = b.word) : a = b := by
  cases a with
  | mk p f =>
    cases b with
    | mk q g =>
      dsimp only at hp
      cases hp
      have : f = g := Dynamic.word_injective _ p hw
      cases this
      rfl

/-- Composition acts on the actual graph maps, not on their images or traces. -/
def preWord {X : Graph.{w}} {c : Component V}
    (m : Graph.Hom X (D.component c)) (a : D.MapOp c) :
    List (Σ d, Graph.Hom X (D.component d)) :=
  a.word.map (fun x => ⟨x.1, m.comp x.2⟩)

theorem preWord_eq {X : Graph.{w}} {c : Component V}
    (m : Graph.Hom X (D.component c)) (a : D.MapOp c) :
    preWord m a = Dynamic.word (fun d => Graph.Hom X (D.component d))
      a.profile (fun i => m.comp (a.maps i)) := by
  unfold preWord word Dynamic.word
  rw [collect_map]
  rfl

theorem preWord_cast {X : Graph.{w}} {c d : Component V} (e : c = d)
    (m : Graph.Hom X (D.component c)) (a : D.MapOp c) :
    preWord (occurrenceTransport (fun c => Graph.Hom X (D.component c)) e m)
      (occurrenceTransport D.MapOp e a) = preWord m a := by cases e; rfl

def collection : Collection V where
  Op := D.MapOp
  profile a := a.profile

def identity (c : Component V) : D.MapOp c where
  profile := c.edge.toPath
  maps := fun i => match i with
    | .inl e => nomatch e
    | .inr () => Graph.Hom.id _

def subst {c : Component V} (a : D.MapOp c)
    (f : ∀ i : Slot a.profile, D.MapOp (componentAt a.profile i)) : D.MapOp c where
  profile := expand a.profile (fun i => (f i).profile)
  maps := joinFamily (fun d => Graph.Hom (D.component c) (D.component d)) a.profile (fun i => (f i).profile)
    (fun i j => (a.maps i).comp ((f i).maps j))

def calcData : CalcData V where
  toCollection := collection (D := D)
  identity := identity (D := D)
  profile_identity _ := rfl
  subst := subst (D := D)
  profile_subst _ _ := rfl

theorem word_subst {c : Component V} (a : D.MapOp c)
    (f : ∀ i : Slot a.profile, D.MapOp (componentAt a.profile i)) :
    (subst a f).word = collect a.profile (fun i => preWord (a.maps i) (f i)) := by
  unfold word subst
  rw [word_joinFamily]
  congr 1
  funext i
  exact (preWord_eq _ _).symm

theorem preWord_subst {X : Graph.{w}} {c : Component V}
    (m : Graph.Hom X (D.component c)) (a : D.MapOp c)
    (f : ∀ i : Slot a.profile, D.MapOp (componentAt a.profile i)) :
    preWord m (subst a f) =
      collect a.profile (fun i => preWord (m.comp (a.maps i)) (f i)) := by
  unfold preWord
  rw [word_subst, collect_map]
  congr 1
  funext i
  unfold preWord
  rw [List.map_map]
  rfl

theorem subst_assoc {c : Component V} (a : D.MapOp c)
    (f : (collection (D := D)).Family a.profile)
    (h : (collection (D := D)).Family (subst a f).profile) :
    subst (subst a f) h = subst a ((calcData (D := D)).composeFamily a f h) := by
  apply ext_word
  · exact (calcData (D := D)).composeAt_profile f h
  · rw [word_subst, word_subst]
    change collect (expand a.profile (fun i => (f i).profile)) _ = _
    rw [collect_expand_slots]
    congr 1
    funext i
    change collect (f i).profile _ = preWord (a.maps i)
      (subst (f i) (expandFamily D.MapOp a.profile (fun i => (f i).profile) h i))
    rw [preWord_subst]
    congr 1
    funext j
    let e := componentAt_slotExpand_symm a.profile (fun i => (f i).profile) ⟨i,j⟩
    have hc := preWord_cast e
      ((subst a f).maps ((slotExpand a.profile (fun i => (f i).profile)).symm ⟨i,j⟩))
      (h ((slotExpand a.profile (fun i => (f i).profile)).symm ⟨i,j⟩))
    change preWord (expandFamily (fun d => Graph.Hom (D.component c) (D.component d))
      a.profile (fun i => (f i).profile) (subst a f).maps i j)
      (expandFamily D.MapOp a.profile (fun i => (f i).profile) h i j) = _ at hc
    rw [show (subst a f).maps = joinFamily (fun d => Graph.Hom (D.component c) (D.component d)) a.profile (fun i => (f i).profile)
      (fun i j => (a.maps i).comp ((f i).maps j)) from rfl,
      expandFamily_joinFamily] at hc
    exact hc.symm

@[simp] theorem preWord_identity {X : Graph.{w}} {c : Component V}
    (m : Graph.Hom X (D.component c)) :
    preWord m (identity c) = [⟨c,m⟩] := rfl

@[simp] theorem preWord_id {c : Component V} (a : D.MapOp c) :
    preWord (Graph.Hom.id (D.component c)) a = a.word := by
  unfold preWord
  change List.map id a.word = a.word
  exact List.map_id a.word

theorem subst_identity {c : Component V} (a : D.MapOp c) :
    subst a ((calcData (D := D)).identityFamily a.profile) = a := by
  apply ext_word
  · exact Path.expand_edges a.profile
  · rw [word_subst]
    rfl

theorem identity_subst {c : Component V} (a : D.MapOp c) :
    subst (identity c) ((collection (D := D)).singletonFamily a) = a := by
  apply ext_word
  · exact Quiver.Path.nil_comp a.profile
  · rw [word_subst]
    exact preWord_id a

/-- All coordinate families form the ambient graph-map calculus. The dynamic
calculus below restricts these by the full fine-boundary equations. -/
def calculus : Calc V where
  toCalcData := calcData (D := D)
  subst_identity := subst_identity
  identity_subst := identity_subst
  subst_assoc := subst_assoc

end MapOp
end Assignment
end WitnessedDecompositions.Dynamic
