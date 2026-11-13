module

public import WitnessedDecompositions.PathOccurrences

/-!
# Graphs, graph maps, and boundary-compatible occurrence families

Both states and actual event records are retained. No finiteness, inhabitance,
reconstructibility, or simplicity hypothesis is imposed on a graph.
-/

@[expose] public section

universe u v w
namespace WitnessedDecompositions.Dynamic

structure Graph where
  State : Type w
  Event : Type w
  source : Event → State
  target : Event → State

namespace Graph

structure Hom (X Y : Graph.{w}) where
  state : X.State → Y.State
  event : X.Event → Y.Event
  source_comm : ∀ e, state (X.source e) = Y.source (event e)
  target_comm : ∀ e, state (X.target e) = Y.target (event e)

namespace Hom
variable {X Y Z T : Graph.{w}}

@[ext] theorem ext {f g : Hom X Y} (hs : f.state = g.state)
    (he : f.event = g.event) : f = g := by
  cases f
  cases g
  cases hs
  cases he
  rfl

def id (X : Graph.{w}) : Hom X X where
  state := fun x => x
  event := fun x => x
  source_comm _ := rfl
  target_comm _ := rfl

/-- Forward-order graph-map composition. -/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  state := g.state ∘ f.state
  event := g.event ∘ f.event
  source_comm e := (congrArg g.state (f.source_comm e)).trans (g.source_comm (f.event e))
  target_comm e := (congrArg g.state (f.target_comm e)).trans (g.target_comm (f.event e))

@[simp] theorem id_comp (f : Hom X Y) : (id X).comp f = f := rfl
@[simp] theorem comp_id (f : Hom X Y) : f.comp (id Y) = f := rfl
@[simp] theorem comp_assoc (f : Hom X Y) (g : Hom Y Z) (h : Hom Z T) :
    (f.comp g).comp h = f.comp (g.comp h) := rfl

end Hom

/-- Exactness retains inverse functions on states and on actual records. -/
def IsIso {X Y : Graph.{w}} (f : Hom X Y) : Prop :=
  ∃ g : Hom Y X, f.comp g = Hom.id X ∧ g.comp f = Hom.id Y

@[simp] theorem isIso_id (X : Graph.{w}) : IsIso (Hom.id X) :=
  ⟨Hom.id X, rfl, rfl⟩

theorem isIso_comp {X Y Z : Graph.{w}} {f : Hom X Y} {g : Hom Y Z}
    (hf : IsIso f) (hg : IsIso g) : IsIso (f.comp g) := by
  obtain ⟨fi, hfi, hif⟩ := hf
  obtain ⟨gi, hgi, hig⟩ := hg
  refine ⟨gi.comp fi, ?_, ?_⟩
  · rw [Hom.comp_assoc, ← Hom.comp_assoc g, hgi, Hom.id_comp, hfi]
  · rw [Hom.comp_assoc, ← Hom.comp_assoc fi, hif, Hom.id_comp, hig]

/-- Graph-map isomorphism is exactly bijectivity on both states and actual
records. Event bijectivity cannot be replaced by visible-behavior equality. -/
theorem isIso_iff_bijective {X Y : Graph.{w}} (f : Hom X Y) :
    IsIso f ↔ Function.Bijective f.state ∧ Function.Bijective f.event := by
  constructor
  · rintro ⟨g, hfg, hgf⟩
    constructor
    · exact Function.bijective_iff_has_inverse.mpr
        ⟨g.state, fun x => congrFun (congrArg Hom.state hfg) x,
          fun y => congrFun (congrArg Hom.state hgf) y⟩
    · exact Function.bijective_iff_has_inverse.mpr
        ⟨g.event, fun x => congrFun (congrArg Hom.event hfg) x,
          fun y => congrFun (congrArg Hom.event hgf) y⟩
  · rintro ⟨hs, he⟩
    obtain ⟨gs, hsl, hsr⟩ := Function.bijective_iff_has_inverse.mp hs
    obtain ⟨ge, hel, her⟩ := Function.bijective_iff_has_inverse.mp he
    let g : Hom Y X :=
      { state := gs
        event := ge
        source_comm := by
          intro e
          apply hs.1
          rw [hsr, f.source_comm, her]
        target_comm := by
          intro e
          apply hs.1
          rw [hsr, f.target_comm, her] }
    refine ⟨g, ?_, ?_⟩
    · apply Hom.ext
      · funext x; exact hsl x
      · funext x; exact hel x
    · apply Hom.ext
      · funext y; exact hsr y
      · funext y; exact her y

/-- The actual sortwise pullback graph, including event multiplicities. -/
def pullback {X Y Z : Graph.{w}} (f : Hom X Z) (g : Hom Y Z) : Graph.{w} where
  State := {xy : X.State × Y.State // f.state xy.1 = g.state xy.2}
  Event := {xy : X.Event × Y.Event // f.event xy.1 = g.event xy.2}
  source xy := ⟨(X.source xy.val.1, Y.source xy.val.2),
    (f.source_comm _).trans ((congrArg Z.source xy.property).trans (g.source_comm _).symm)⟩
  target xy := ⟨(X.target xy.val.1, Y.target xy.val.2),
    (f.target_comm _).trans ((congrArg Z.target xy.property).trans (g.target_comm _).symm)⟩

namespace pullback
variable {X Y Z T : Graph.{w}} (f : Hom X Z) (g : Hom Y Z)

def fst : Hom (pullback f g) X where
  state xy := xy.val.1
  event xy := xy.val.1
  source_comm _ := rfl
  target_comm _ := rfl

def snd : Hom (pullback f g) Y where
  state xy := xy.val.2
  event xy := xy.val.2
  source_comm _ := rfl
  target_comm _ := rfl

@[simp] theorem condition : (fst f g).comp f = (snd f g).comp g := by
  apply Hom.ext
  · funext xy; exact xy.property
  · funext xy; exact xy.property

def lift (a : Hom T X) (b : Hom T Y) (h : a.comp f = b.comp g) :
    Hom T (pullback f g) where
  state x := ⟨(a.state x, b.state x), congrFun (congrArg Hom.state h) x⟩
  event x := ⟨(a.event x, b.event x), congrFun (congrArg Hom.event h) x⟩
  source_comm e := by
    apply Subtype.ext
    exact Prod.ext (a.source_comm e) (b.source_comm e)
  target_comm e := by
    apply Subtype.ext
    exact Prod.ext (a.target_comm e) (b.target_comm e)

@[simp] theorem lift_fst (a : Hom T X) (b : Hom T Y) (h : a.comp f = b.comp g) :
    (lift f g a b h).comp (fst f g) = a := rfl
@[simp] theorem lift_snd (a : Hom T X) (b : Hom T Y) (h : a.comp f = b.comp g) :
    (lift f g a b h).comp (snd f g) = b := rfl

@[ext] theorem hom_ext {a b : Hom T (pullback f g)}
    (h₁ : a.comp (fst f g) = b.comp (fst f g))
    (h₂ : a.comp (snd f g) = b.comp (snd f g)) : a = b := by
  apply Hom.ext
  · funext x
    apply Subtype.ext
    exact Prod.ext (congrFun (congrArg Hom.state h₁) x)
      (congrFun (congrArg Hom.state h₂) x)
  · funext x
    apply Subtype.ext
    exact Prod.ext (congrFun (congrArg Hom.event h₁) x)
      (congrFun (congrArg Hom.event h₂) x)

end pullback
end Graph

/-- Graph spans assigned to the unchanged syntactic interfaces and components. -/
structure Assignment (V : Type u) [Quiver.{v} V] where
  boundary : V → Graph.{w}
  component : Component V → Graph.{w}
  left : ∀ c, Graph.Hom (component c) (boundary c.source)
  right : ∀ c, Graph.Hom (component c) (boundary c.target)

namespace Assignment
variable {V : Type u} [Quiver.{v} V]

abbrev Family (D : Assignment.{u, v, w} V) (X : Graph.{w})
    {a b : V} (p : Quiver.Path a b) :=
  ∀ i : Path.Slot p, Graph.Hom X (D.component (Path.componentAt p i))

/-- Fine boundary equations, including the retained boundary equation at nil. -/
def Compatible (D : Assignment.{u, v, w} V) (X : Graph.{w}) {a : V} :
    {b : V} → (p : Quiver.Path a b) → D.Family X p →
      Graph.Hom X (D.boundary a) → Graph.Hom X (D.boundary b) → Prop
  | _, .nil, _, h, k => h = k
  | _, .cons p _, f, h, k =>
      D.Compatible X p (fun i => f (.inl i)) h ((f (.inr ())).comp (D.left _)) ∧
      (f (.inr ())).comp (D.right _) = k

@[simp] theorem compatible_nil (D : Assignment.{u, v, w} V) (X : Graph.{w})
    {a : V} (f : D.Family X (Quiver.Path.nil : Quiver.Path a a))
    (h k : Graph.Hom X (D.boundary a)) :
    D.Compatible X .nil f h k ↔ h = k := Iff.rfl

/-- Precomposition preserves every fine boundary equation, including nil. -/
theorem compatible_precomp (D : Assignment.{u, v, w} V) {X Y : Graph.{w}}
    {a b : V} (p : Quiver.Path a b) (f : D.Family X p)
    (h : Graph.Hom X (D.boundary a)) (k : Graph.Hom X (D.boundary b))
    (hc : D.Compatible X p f h k) (q : Graph.Hom Y X) :
    D.Compatible Y p (fun i => q.comp (f i)) (q.comp h) (q.comp k) := by
  induction p with
  | nil => exact congrArg (fun t => q.comp t) hc
  | cons p e ih =>
      exact ⟨ih (fun i => f (.inl i)) ((f (.inr ())).comp (D.left _)) hc.1,
        congrArg (fun t => q.comp t) hc.2⟩

end Assignment
end WitnessedDecompositions.Dynamic
