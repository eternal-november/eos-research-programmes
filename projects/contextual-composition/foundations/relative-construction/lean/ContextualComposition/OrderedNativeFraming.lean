module
public import ContextualComposition.ConstantCollectionFraming
public import ContextualComposition.NativeFinitePush
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! Ordinary-data framing in the ordered-collection presentation. The
native context at each input is an actual augmented family and each
context-square component is the original augmentation-preserving map. -/

@[expose] public section
namespace ContextualComposition.OrderedNativeFraming
open CategoryTheory NativeFinitePush ConstantCollectionFraming OrderedArityReflection
universe u v
variable {V : Type u} {K : Coeff.{u,v} V} {P : Push K} {I : V}
variable {A B C D A' B' C' D' X Y Z : Type u}
abbrev Pos (p : Aug P I) := Fin p.base.n

structure Operation (P : Push K) (I : V) (A B : Type u) where
  ctx : A → Aug P I
  collection : Collection.{u}
  body : ∀ a, Pos (ctx a) → Point collection B

structure Square {F : Operation P I A B} {G : Operation P I A' B'} (f : A → A') (g : B → B') where
  context : ∀ a, AugHom P (F.ctx a) (G.ctx (f a))
  shape : F.collection ⟶ G.collection
  body : ∀ a p, (G.body (f a) ((context a).native.addr p)) =
    (change shape).app B' ((extF F.collection).map (TypeCat.ofHom g) (F.body a p))

@[ext] theorem Square.ext {F : Operation P I A B} {G : Operation P I A' B'} {f : A → A'} {g : B → B'}
    {s t : Square (F := F) (G := G) f g} (hs : s.context = t.context) (hr : s.shape = t.shape) : s = t := by
  cases s; cases t; cases hs; cases hr; rfl

def idSquare (F : Operation P I A B) : Square (F := F) (G := F) id id :=
  ⟨fun _ => AugHom.ident _,𝟙 _,fun _ _ => rfl⟩

def vert {F : Operation P I A B} {G : Operation P I A' B'} {H : Operation P I C D}
    {f : A → A'} {g : B → B'} {f' : A' → C} {g' : B' → D}
    (s : Square (F := F) (G := G) f g) (t : Square (F := G) (G := H) f' g') :
    Square (F := F) (G := H) (f' ∘ f) (g' ∘ g) where
  context a := (s.context a).comp (t.context (f a))
  shape := s.shape ≫ t.shape
  body a p := (t.body _ _).trans (congrArg (fun z => (change t.shape).app D
    ((extF G.collection).map (TypeCat.ofHom g') z)) (s.body a p))

def frameOp (X : Type u) (F : Operation P I A B) : Operation P I (X × A) (X × B) where
  ctx z := F.ctx z.2
  collection := F.collection
  body z p := (CanonicalSetStrength.strength (extF F.collection) X).app B (z.1,F.body z.2 p)

abbrev Total (F : Operation P I A B) := Σ a, Pos (F.ctx a)
def project (F : Operation P I A B) : Total F ⟶ A := TypeCat.ofHom Sigma.fst
def dropFrame (X : Type u) (F : Operation P I A B) : Total (frameOp X F) ⟶ Total F :=
  TypeCat.ofHom fun z => ⟨z.1.2,z.2⟩

theorem projection_pullback (X : Type u) (F : Operation P I A B) :
    IsPullback (dropFrame X F) (project (frameOp X F)) (project F) (TypeCat.ofHom Prod.snd) := by
  apply (Limits.Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl,?_,?_⟩
  · rintro ⟨⟨x,a⟩,w⟩ ⟨⟨y,b⟩,v⟩ ⟨ht,hb⟩
    change (x,a) = (y,b) at hb
    cases hb
    exact congrArg (fun z : Total F => (Sigma.mk (x,z.1) z.2 : Total (frameOp X F))) ht
  · rintro ⟨a,w⟩ ⟨x,b⟩ h
    change a = b at h
    subst b
    exact ⟨⟨(x,a),w⟩,rfl,rfl⟩

theorem projection_admitted (J : MorphismProperty (Type u)) [J.IsStableUnderBaseChange]
    (X : Type u) (F : Operation P I A B) (h : J (project F)) : J (project (frameOp X F)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (projection_pullback X F) h

def frameSquare (X : Type u) {F : Operation P I A B} {G : Operation P I A' B'}
    {f : A → A'} {g : B → B'} (s : Square (F := F) (G := G) f g) :
    Square (F := frameOp X F) (G := frameOp X G) (Prod.map id f) (Prod.map id g) where
  context z := s.context z.2
  shape := s.shape
  body z p := congrArg (fun a => (CanonicalSetStrength.strength (extF G.collection) X).app B' (z.1,a)) (s.body z.2 p)

def parameterSquare (h : X → Y) (F : Operation P I A B) :
    Square (F := frameOp X F) (G := frameOp Y F) (Prod.map h id) (Prod.map h id) :=
  ⟨fun _ => AugHom.ident _,𝟙 _,fun _ _ => rfl⟩

theorem frame_id (X : Type u) (F : Operation P I A B) :
    frameSquare X (idSquare F) = idSquare (frameOp X F) := rfl

theorem frame_vertical (X : Type u) {F : Operation P I A B} {G : Operation P I A' B'} {H : Operation P I C D}
    {f : A → A'} {g : B → B'} {f' : A' → C} {g' : B' → D}
    (s : Square (F := F) (G := G) f g) (t : Square (F := G) (G := H) f' g') :
    frameSquare X (vert s t) = vert (frameSquare X s) (frameSquare X t) := rfl

theorem parameter_comp (q : X → Y) (r : Y → Z) (F : Operation P I A B) :
    vert (parameterSquare q F) (parameterSquare r F) = parameterSquare (r ∘ q) F :=
  Square.ext (funext fun _ => AugHom.ident_comp _) rfl

theorem parameter_naturality (h : X → Y) {F : Operation P I A B} {G : Operation P I A' B'}
    {f : A → A'} {g : B → B'} (s : Square (F := F) (G := G) f g) :
    vert (frameSquare X s) (parameterSquare h G) = vert (parameterSquare h F) (frameSquare Y s) :=
  Square.ext (funext fun z => (AugHom.comp_ident (s.context z.2)).trans (AugHom.ident_comp _).symm) rfl

theorem framed_native_map (X : Type u) {F : Operation P I A B} {G : Operation P I A' B'}
    {f : A → A'} {g : B → B'} (s : Square (F := F) (G := G) f g) (z : X × A) :
    (frameSquare X s).context z = s.context z.2 := rfl

/-- Move a native operation to the common endpoint before comparing parameter routes. -/
def pre (u : A' → A) (F : Operation P I A B) : Operation P I A' B :=
  ⟨fun a => F.ctx (u a),F.collection,fun a => F.body (u a)⟩
def post (F : Operation P I A B) (v : B → B') : Operation P I A B' :=
  ⟨F.ctx,F.collection,fun a p => (extF F.collection).map (TypeCat.ofHom v) (F.body a p)⟩

theorem parameter_exact (h : X → Y) (F : Operation P I A B) :
    post (frameOp X F) (Prod.map h id) = pre (Prod.map h id) (frameOp Y F) := rfl

theorem unit_exact (F : Operation P I A B) :
    post (frameOp PUnit.{u+1} F) Prod.snd = pre Prod.snd F := rfl

theorem assoc_exact (X Y : Type u) (F : Operation P I A B) :
    post (frameOp X (frameOp Y F)) (fun (p : X × Y × B) => ((p.1,p.2.1),p.2.2)) =
      pre (fun (p : X × Y × A) => ((p.1,p.2.1),p.2.2)) (frameOp (X × Y) F) := rfl

/-- The independent ordered occurrences and dependent serial assembly
supplied by the O1 context calculus. These operations have no frame
parameter. Their readouts expose every native raw position. -/
structure ContextOps (P : Push K) (I : V) where
  occurrence : (n : Nat) → (Fin n → Aug P I) → Aug P I
  occurrencePos : ∀ n R, Pos (occurrence n R) ≃ (∀ i, Pos (R i))
  occurrenceMap : ∀ n {R R' : Fin n → Aug P I}, (∀ i, AugHom P (R i) (R' i)) →
    AugHom P (occurrence n R) (occurrence n R')
  dependent : (R : Aug P I) → (Pos R → Aug P I) → Aug P I
  dependentPos : ∀ R S, Pos (dependent R S) ≃ (Σ x : Pos R, Pos (S x))

variable (O : ContextOps P I)

def occurrenceAt {G : Collection.{u}} (R : B → Aug P I) (z : Point G B) :=
  O.occurrence z.arity (fun i => R (z.label i))

/-- The entire augmented family is equal on the two crossing routes.
The comparison is over the image of the fixed-frame strength. -/
theorem crossing_object {G : Collection.{u}} (R : B → Aug P I) (x : X) (z : Point G B) :
    occurrenceAt O (fun xb : X × B => R xb.2) ((CanonicalSetStrength.strength (extF G) X).app B (x,z)) =
      occurrenceAt O R z := rfl

theorem crossing_native {G : Collection.{u}} (R R' : B → Aug P I) (k : ∀ b, AugHom P (R b) (R' b)) (x : X) (z : Point G B) :
    (let z' := (CanonicalSetStrength.strength (extF G) X).app B (x,z)
     O.occurrenceMap z'.arity (fun i => k (z'.label i).2)) =
      O.occurrenceMap z.arity (fun i => k (z.label i)) := rfl

/-- The actual crossed body pairs each displayed occurrence with the
specific raw sample at that occurrence. -/
def cross {G : Collection.{u}} (R : B → Aug P I) (z : Point G B) (w : Pos (occurrenceAt O R z)) :
    Point G (Σ b, Pos (R b)) :=
  ⟨z.arity,z.shape,fun i => ⟨z.label i,O.occurrencePos _ _ w i⟩⟩

theorem crossing_body {G : Collection.{u}} (R : B → Aug P I) (z : Point G B) (x : X) (w : Pos (occurrenceAt O R z)) :
    (extF G).map (TypeCat.ofHom (fun (p : Σ xb : X × B, Pos (R xb.2)) => (p.1.1, Sigma.mk p.1.2 p.2)))
      (cross O (fun xb : X × B => R xb.2) ((CanonicalSetStrength.strength (extF G) X).app B (x,z)) w) =
      (CanonicalSetStrength.strength (extF G) X).app _ (x,cross O R z w) := rfl

structure AugIso (a b : Aug P I) where
  hom : AugHom P a b
  inv : AugHom P b a
  hom_inv : hom.comp inv = AugHom.ident a
  inv_hom : inv.comp hom = AugHom.ident b

/-- Native components of the four independently supplied crossing
modifications. Their inputs are addressed augmented families, without any
assumption about external Set frames. The second-stage family in the
Fubini target is indexed by the retained outer witness. -/
structure CrossingComparisons (O : ContextOps P I) where
  unit : Aug P I
  contextUnit : ∀ n, AugIso (O.occurrence n (fun _ => unit)) unit
  contentUnit : ∀ r, AugIso (O.occurrence 1 (fun _ => r)) r
  contextAccum : ∀ n (r : Fin n → Aug P I) (s : ∀ i, Pos (r i) → Aug P I),
    AugIso (O.occurrence n (fun i => O.dependent (r i) (s i)))
      (O.dependent (O.occurrence n r) (fun w => O.occurrence n (fun i => s i (O.occurrencePos n r w i))))
  contentAccum : ∀ n (m : Fin n → Nat) (r : ∀ i, Fin (m i) → Aug P I),
    AugIso (O.occurrence n (fun i => O.occurrence (m i) (r i)))
      (O.occurrence (∑ i, m i) (fun j => let a := (finSigmaFinEquiv (n := m)).symm j; r a.1 a.2))

variable (L : CrossingComparisons O)

theorem context_unit_frame {G : Collection.{u}} (z : Point G B) (x : X) :
    L.contextUnit (((CanonicalSetStrength.strength (extF G) X).app B (x,z)).arity) = L.contextUnit z.arity := rfl

theorem content_unit_frame (r : B → Aug P I) (b : B) (x : X) :
    (let tagged : X × B → Aug P I := fun xb => r xb.2; L.contentUnit (tagged (x,b))) = L.contentUnit (r b) := rfl

theorem context_accumulation_frame {G : Collection.{u}} (z : Point G B) (x : X)
    (r : B → Aug P I) (s : ∀ b, Pos (r b) → Aug P I) :
    (let z' := (CanonicalSetStrength.strength (extF G) X).app B (x,z)
     L.contextAccum z'.arity (fun i => r (z'.label i).2) (fun i => s (z'.label i).2)) =
      L.contextAccum z.arity (fun i => r (z.label i)) (fun i => s (z.label i)) := rfl

theorem content_accumulation_frame {G G' : Collection.{u}} (z : Point G (Point G' B)) (x : X) (r : B → Aug P I) :
    (let z' := (extF G).map ((CanonicalSetStrength.strength (extF G') X).app B)
       ((CanonicalSetStrength.strength (extF G) X).app _ (x,z))
     L.contentAccum z'.arity (fun i => (z'.label i).arity) (fun i j => r ((z'.label i).label j).2)) =
      L.contentAccum z.arity (fun i => (z.label i).arity) (fun i j => r ((z.label i).label j)) := rfl

def compose (F : Operation P I A B) (G : Operation P I B C) : Operation P I A C where
  collection := sub F.collection G.collection
  ctx a := O.dependent (F.ctx a) (fun p => occurrenceAt O G.ctx (F.body a p))
  body a w :=
    let z := O.dependentPos (F.ctx a) (fun p => occurrenceAt O G.ctx (F.body a p)) w
    let r := F.body a z.1
    let children := O.occurrencePos r.arity (fun i => G.ctx (r.label i)) z.2
    pack ⟨r.arity,r.shape,fun i => G.body (r.label i) (children i)⟩

/-- The sequential comparison in the fixed presentation is an equality
of the entire native output, with the original grade at dormant shapes. -/
theorem serial_exact (X : Type u) (F : Operation P I A B) (G : Operation P I B C) :
    compose O (frameOp X F) (frameOp X G) = frameOp X (compose O F G) := rfl

theorem framed_composite_admitted (J : MorphismProperty (Type u)) [J.IsStableUnderBaseChange]
    (X : Type u) (F : Operation P I A B) (G : Operation P I B C) (admitted : J (project (compose O F G))) :
    J (project (compose O (frameOp X F) (frameOp X G))) :=
  projection_admitted J X (compose O F G) admitted

/-- Native action on serial maps and its readout on retained positions,
and the analogous readout for the independently supplied occurrence maps. -/
structure MapOps (O : ContextOps P I) where
  occurrence_read : ∀ n {r r' : Fin n → Aug P I} (t : ∀ i, AugHom P (r i) (r' i)) w,
    O.occurrencePos n r' ((O.occurrenceMap n t).native.addr w) =
      fun i => (t i).native.addr (O.occurrencePos n r w i)
  dependentMap : ∀ {r r' : Aug P I} {s : Pos r → Aug P I} {s' : Pos r' → Aug P I}
    (f : AugHom P r r'), (∀ p, AugHom P (s p) (s' (f.native.addr p))) → AugHom P (O.dependent r s) (O.dependent r' s')
  dependent_read : ∀ {r r' : Aug P I} {s : Pos r → Aug P I} {s' : Pos r' → Aug P I}
    (f : AugHom P r r') (g : ∀ p, AugHom P (s p) (s' (f.native.addr p))) w,
    O.dependentPos r' s' ((dependentMap f g).native.addr w) =
      (let z := O.dependentPos r s w; ⟨f.native.addr z.1,(g z.1).native.addr z.2⟩)

variable (M : MapOps O)

def actPoint {G G' : Collection.{u}} (s : G ⟶ G') (g : B → B') (z : Point G B) : Point G' B' :=
  (change s).app B' ((extF G).map (TypeCat.ofHom g) z)

/-- Transport only at the resulting augmented family. The transports
therefore retain the whole coefficient and augmentation comparison. -/
def crossedMap {U U' : Collection.{u}} (R : B → Aug P I) (R' : B' → Aug P I) (c : U ⟶ U') (g : B → B')
    (k : ∀ b, AugHom P (R b) (R' (g b))) (z : Point U B) (z' : Point U' B') (h : z' = actPoint c g z) :
    AugHom P (occurrenceAt O R z) (occurrenceAt O R' z') :=
  cast (congrArg (AugHom P (occurrenceAt O R z)) (congrArg (occurrenceAt O R') h.symm))
    (O.occurrenceMap z.arity (fun i => k (z.label i)))

def children {U : Collection.{u}} (G : Operation P I B C) (z : Point U B)
    (w : Pos (occurrenceAt O G.ctx z)) : Point U (Point G.collection C) :=
  ⟨z.arity,z.shape,fun i => G.body (z.label i) (O.occurrencePos z.arity (fun i => G.ctx (z.label i)) w i)⟩

include M in
theorem child_square {U U' : Collection.{u}} (p : U ⟶ U') {g : B → B'} {v : C → C'}
    {G : Operation P I B C} {G' : Operation P I B' C'} (t : Square (F := G) (G := G') g v)
    (z : Point U B) (z' : Point U' B') (e : z' = actPoint p g z) (w : Pos (occurrenceAt O G.ctx z)) :
    children O G' z' ((crossedMap O G.ctx G'.ctx p g t.context z z' e).native.addr w) =
      actPoint p (actPoint t.shape v) (children O G z w) := by
  subst z'
  refine congrArg (Point.mk z.arity (p _ z.shape)) (funext fun i => ?_)
  change Fin z.arity at i
  change G'.body (g (z.label i)) (O.occurrencePos _ _ ((O.occurrenceMap z.arity (fun i => t.context (z.label i))).native.addr w) i) = _
  exact (congrArg (G'.body _) (congrFun (M.occurrence_read z.arity (fun i => t.context (z.label i)) w) i)).trans (t.body _ _)

def composedContext {F : Operation P I A B} {F' : Operation P I A' B'} {G : Operation P I B C} {G' : Operation P I B' C'}
    {f : A → A'} {g : B → B'} {v : C → C'} (s : Square (F := F) (G := F') f g) (t : Square (F := G) (G := G') g v) (a : A) :
    AugHom P ((compose O F G).ctx a) ((compose O F' G').ctx (f a)) :=
  M.dependentMap (s.context a) (fun w => crossedMap O G.ctx G'.ctx s.shape g t.context _ _ (s.body a w))

def horizontal {F : Operation P I A B} {F' : Operation P I A' B'} {G : Operation P I B C} {G' : Operation P I B' C'}
    {f : A → A'} {g : B → B'} {v : C → C'} (s : Square (F := F) (G := F') f g) (t : Square (F := G) (G := G') g v) :
    Square (F := compose O F G) (G := compose O F' G') f v where
  context := composedContext O M s t
  shape := subMap s.shape t.shape
  body a w := by
    let p := O.dependentPos (F.ctx a) (fun p => occurrenceAt O G.ctx (F.body a p)) w
    let lift := fun x => crossedMap O G.ctx G'.ctx s.shape g t.context _ _ (s.body a x)
    let body := fun (z : Σ x : Pos (F'.ctx (f a)), Pos (occurrenceAt O G'.ctx (F'.body (f a) x))) =>
      pack (children O G' (F'.body (f a) z.1) z.2)
    have read := congrArg body (M.dependent_read (s.context a) lift w)
    exact read.trans (congrArg pack (child_square O M s.shape t _ _ (s.body a p.1) p.2))

/-- Naturality of the sequential comparison is an equality of complete
squares, including every aggregated coefficient arrow. Proof transports
in the two paths occur between the same native families. -/
theorem frame_horizontal (X : Type u)
    {F : Operation P I A B} {F' : Operation P I A' B'} {G : Operation P I B C} {G' : Operation P I B' C'}
    {f : A → A'} {g : B → B'} {v : C → C'} (s : Square (F := F) (G := F') f g) (t : Square (F := G) (G := G') g v) :
    frameSquare X (horizontal O M s t) = horizontal O M (frameSquare X s) (frameSquare X t) := rfl

/-- A comparison diagram built from native squares may be checked after
framing by reducing its two routes to the unframed pastes. The preceding
identity, vertical and horizontal equations establish those reductions
for composites of the primitive squares. -/
theorem preserve_pasting (X : Type u) {F : Operation P I A B} {G : Operation P I A' B'}
    {u : A → A'} {v : B → B'} {s t : Square (F := F) (G := G) u v}
    {s' t' : Square (F := frameOp X F) (G := frameOp X G) (Prod.map id u) (Prod.map id v)}
    (ls : s' = frameSquare X s) (lt : t' = frameSquare X t) (law : s = t) : s' = t' :=
  ls.trans ((congrArg (frameSquare X) law).trans lt.symm)

theorem pure_exact (X : Type u) (U : Aug P I) (f : A → B) :
    let pure {A B : Type u} (h : A → B) : Operation P I A B :=
      ⟨fun _ => U,OrderedArityReflection.identity,fun a _ => ⟨1,⟨⟨rfl⟩⟩,fun _ => h a⟩⟩
    frameOp X (pure f) = pure (Prod.map id f) := rfl

end ContextualComposition.OrderedNativeFraming
