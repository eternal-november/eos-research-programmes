module
public import ContextualComposition.OrderedNativeFrameAction
public import ContextualComposition.OrderedLeafReadout

/-! The lax section in the native ordered-collection presentation:
full context witnesses and coefficients survive, while the grade map
for sequential composition forgets the ordered partition. -/

@[expose] public section
namespace ContextualComposition.OrderedArityAssembly
open CategoryTheory NativeFinitePush OrderedArityReflection ConstantCollectionFraming OrderedNativeFraming
universe u v
set_option backward.isDefEq.respectTransparency false
variable {V : Type u} {K : Coeff.{u,v} V} {P : Push K} {I : V}
variable {A B C X : Type u}

structure Fixed (P : Push K) (I : V) (A B : Type u) where
  ctx : A → Aug P I
  body : ∀ a, Pos (ctx a) → Point terminal B

def includeFixed (F : Fixed P I A B) : Operation P I A B := ⟨F.ctx,terminal,F.body⟩

def strip (F : Operation P I A B) : Fixed P I A B :=
  ⟨F.ctx,fun a w => (change (forgetShape F.collection)).app B (F.body a w)⟩

theorem strip_include (F : Fixed P I A B) : strip (includeFixed F) = F := rfl

variable (O : ContextOps P I)

/-- Fixed-list composition, on the same raw addressed witnesses. The
readout below identifies its ordered dependent sum with list flattening. -/
def fixedSerial (F : Fixed P I A B) (G : Fixed P I B C) : Fixed P I A C where
  ctx a := O.dependent (F.ctx a) (fun p => occurrenceAt O G.ctx (F.body a p))
  body a w :=
    let z := O.dependentPos (F.ctx a) (fun p => occurrenceAt O G.ctx (F.body a p)) w
    let r := F.body a z.1
    let s := O.occurrencePos r.arity (fun i => G.ctx (r.label i)) z.2
    let rows := fun i => G.body (r.label i) (s i)
    let n := fun i => (rows i).arity
    ⟨∑ i, n i,PUnit.unit,fun j => let k := (finSigmaFinEquiv (n := n)).symm j; (rows k.1).label k.2⟩

theorem strip_serial (F : Operation P I A B) (G : Operation P I B C) :
    strip (compose O F G) = fixedSerial O (strip F) (strip G) := rfl

def multiplication (F : Fixed P I A B) (G : Fixed P I B C) :
    compose O (includeFixed F) (includeFixed G) ⟶ includeFixed (fixedSerial O F G) :=
  ⟨fun _ => AugHom.ident _,forgetShape _,fun _ _ => rfl⟩

theorem multiplication_list (F : Fixed P I A B) (G : Fixed P I B C) (a : A)
    (w : Pos ((fixedSerial O F G).ctx a)) :
    let z := O.dependentPos (F.ctx a) (fun p => occurrenceAt O G.ctx (F.body a p)) w
    let r := F.body a z.1
    let q := O.occurrencePos r.arity (fun i => G.ctx (r.label i)) z.2
    listBody ((fixedSerial O F G).body a w) =
      (List.ofFn (fun i => listBody (G.body (r.label i) (q i)))).flatten := by
  intro z r q
  exact OrderedLeafReadout.ragged (fun i => (G.body (r.label i) (q i)).arity)
    (fun i => (G.body (r.label i) (q i)).label)

def grade : Operation P I A B ⥤ Collection where
  obj F := F.collection
  map f := f.shape
  map_id _ := rfl
  map_comp _ _ := rfl

def cutIso (C D : Collection.{u}) : sub C D ≅ substitution C D where
  hom n := cutEquiv C D n
  inv n := (cutEquiv C D n).symm
  hom_inv_id := funext₂ fun n x => (cutEquiv C D n).symm_apply_apply x
  inv_hom_id := funext₂ fun n x => (cutEquiv C D n).apply_symm_apply x

/-- Loss of the ordered shape prevents invertibility of the actual
sequential comparison even when its whole context map is identity. -/
theorem multiplication_not_iso {V : Type} {K : Coeff.{0,v} V} {P : Push K} {I : V}
    (O : ContextOps P I) {A B C : Type} (F : Fixed P I A B) (G : Fixed P I B C) :
    ¬ IsIso (multiplication O F G) := by
  intro h
  let q := (grade (P := P) (I := I) (A := A) (B := C)).map (multiplication O F G)
  have hq : IsIso q := Functor.map_isIso _ _
  have eq : (cutIso terminal terminal).inv ≫ q = mulComparison :=
    @Subsingleton.elim (substitution terminal.{0} terminal ⟶ terminal) _ _ _
  exact mul_not_iso (eq ▸ (inferInstance : IsIso ((cutIso terminal terminal).inv ≫ q)))

def pureFixed (a : Aug P I) (f : A → B) : Fixed P I A B :=
  ⟨fun _ => a,fun x _ => ⟨1,PUnit.unit,fun _ => f x⟩⟩
def pureGraded (a : Aug P I) (f : A → B) : Operation P I A B :=
  ⟨fun _ => a,OrderedArityReflection.identity,fun x _ => unary (f x)⟩

def unit (a : Aug P I) (f : A → B) : pureGraded a f ⟶ includeFixed (pureFixed a f) :=
  ⟨fun _ => AugHom.ident _,unitComparison,fun _ _ => rfl⟩

theorem unit_not_invertible {V : Type} {K : Coeff.{0,v} V} {P : Push K} {I : V} {A B : Type} (a : Aug P I) (f : A → B) :
    ¬ IsIso (unit a f) := fun _ => unit_not_iso (Functor.map_isIso (grade (P := P) (I := I) (A := A) (B := B)) (unit a f))

theorem terminal_target_ext {F : Operation P I A B} {G : Fixed P I A B} {f g : F ⟶ includeFixed G}
    (h : f.context = g.context) : f = g := Square.ext h (@Subsingleton.elim (F.collection ⟶ terminal) _ _ _)

def stripSquare {F G : Operation P I A B} (s : F ⟶ G) : includeFixed (strip F) ⟶ includeFixed (strip G) where
  context := s.context
  shape := 𝟙 _
  body a p := congrArg (fun q => (change (forgetShape G.collection)).app B q) (s.body a p)

theorem multiplication_natural (M : MapOps O) {F F' : Fixed P I A B} {G G' : Fixed P I B C}
    (s : includeFixed F ⟶ includeFixed F') (t : includeFixed G ⟶ includeFixed G') :
    horizontal O M s t ≫ multiplication O F' G' = multiplication O F G ≫ stripSquare (horizontal O M s t) := by
  apply terminal_target_ext
  funext a
  exact (AugHom.comp_ident _).trans (AugHom.ident_comp _).symm

/-- Identity laws for the unframed native occurrence and serial operators.
They express functoriality of the original context operations. -/
structure NativeIdentity (M : MapOps O) : Prop where
  occurrence : ∀ n (r : Fin n → Aug P I), O.occurrenceMap n (fun i => AugHom.ident (r i)) = AugHom.ident _
  dependent : ∀ (r : Aug P I) (q : Pos r → Aug P I),
    M.dependentMap (AugHom.ident r) (s' := q) (fun i => AugHom.ident (q i)) = AugHom.ident _

def discard (F : Operation P I A B) : F ⟶ includeFixed (strip F) :=
  ⟨fun _ => AugHom.ident _,forgetShape _,fun _ _ => rfl⟩

theorem discard_natural {F G : Operation P I A B} (s : F ⟶ G) :
    s ≫ discard G = discard F ≫ stripSquare s := by
  apply terminal_target_ext
  funext a
  exact (AugHom.comp_ident _).trans (AugHom.ident_comp _).symm

theorem discard_id (F : Fixed P I A B) : discard (includeFixed F) = 𝟙 (includeFixed F) := by
  apply terminal_target_ext; rfl

theorem horizontal_discard (M : MapOps O) (laws : NativeIdentity O M)
    (F : Operation P I A B) (G : Operation P I B C) (a : A) :
    (horizontal O M (discard F) (discard G)).context a = AugHom.ident _ := by
  let r := F.ctx a
  let q := fun p => occurrenceAt O G.ctx (F.body a p)
  have compOcc (p : Pos r) :
      crossedMap O G.ctx (includeFixed (strip G)).ctx (discard F).shape id (discard G).context
          (F.body a p) _ ((discard F).body a p) = AugHom.ident (q p) :=
    laws.occurrence (F.body a p).arity (fun i => G.ctx ((F.body a p).label i))
  exact (congrArg (M.dependentMap (AugHom.ident r) (s' := q)) (funext compOcc)).trans (laws.dependent r q)

theorem discard_horizontal (M : MapOps O) (laws : NativeIdentity O M)
    (F : Operation P I A B) (G : Operation P I B C) :
    horizontal O M (discard F) (discard G) ≫ multiplication O (strip F) (strip G) = discard (compose O F G) := by
  apply terminal_target_ext
  funext a
  exact (AugHom.comp_ident _).trans (horizontal_discard O M laws F G a)

/-- The section's pure comparison followed by serial comparison recovers
erasure of the left-unit route, including its full coefficient maps. -/
theorem lax_left_unit (M : MapOps O) (laws : NativeIdentity O M) (t : Aug P I)
    (F : Fixed P I A B) (leftUnit : compose O (pureGraded t (id : A → A)) (includeFixed F) ⟶ includeFixed F) :
    (horizontal O M (unit t (id : A → A)) (discard (includeFixed F)) ≫
      multiplication O (pureFixed t id) F) ≫ stripSquare leftUnit = leftUnit := by
  have h := discard_horizontal O M laws (pureGraded t (id : A → A)) (includeFixed F)
  exact (congrArg (fun p => p ≫ stripSquare leftUnit) h).trans
    ((discard_natural leftUnit).symm.trans ((congrArg (fun p => leftUnit ≫ p) (discard_id F)).trans (Category.comp_id leftUnit)))

theorem lax_right_unit (M : MapOps O) (laws : NativeIdentity O M) (t : Aug P I)
    (F : Fixed P I A B) (rightUnit : compose O (includeFixed F) (pureGraded t (id : B → B)) ⟶ includeFixed F) :
    (horizontal O M (discard (includeFixed F)) (unit t (id : B → B)) ≫
      multiplication O F (pureFixed t id)) ≫ stripSquare rightUnit = rightUnit := by
  have h := discard_horizontal O M laws (includeFixed F) (pureGraded t (id : B → B))
  exact (congrArg (fun p => p ≫ stripSquare rightUnit) h).trans
    ((discard_natural rightUnit).symm.trans ((congrArg (fun p => rightUnit ≫ p) (discard_id F)).trans (Category.comp_id rightUnit)))

def comparisonPaste (M : MapOps O) (F : Operation P I A B) (G : Operation P I B C) :
    compose O F G ⟶ includeFixed (strip (compose O F G)) :=
  horizontal O M (discard F) (discard G) ≫ multiplication O (strip F) (strip G)

/-- Naturality of both comparison pastes, even across distinct intermediate
endpoints. Substitution of the two parenthesizations gives associativity. -/
theorem paste_natural {B' : Type u} (M : MapOps O) (laws : NativeIdentity O M)
    (F : Operation P I A B) (G : Operation P I B C)
    (F' : Operation P I A B') (G' : Operation P I B' C)
    (α : compose O F G ⟶ compose O F' G') :
    comparisonPaste O M F G ≫ stripSquare α = α ≫ comparisonPaste O M F' G' :=
  (congrArg (fun p => p ≫ stripSquare α) (discard_horizontal O M laws F G)).trans
    ((discard_natural α).symm.trans (congrArg (fun p => α ≫ p) (discard_horizontal O M laws F' G').symm))

/-- For any actual O1 associator (or parallel comparison) of the two
retained ternary routes, the section's two multiplication pastes commute
with the fixed-List associator obtained by erasing its shape. This statement
retains that associator's complete native context map. -/
theorem lax_associativity {D : Type u} (M : MapOps O) (laws : NativeIdentity O M)
    (F : Fixed P I A B) (G : Fixed P I B C) (H : Fixed P I C D)
    (α : compose O (compose O (includeFixed F) (includeFixed G)) (includeFixed H) ⟶
      compose O (includeFixed F) (compose O (includeFixed G) (includeFixed H))) :
    comparisonPaste O M (compose O (includeFixed F) (includeFixed G)) (includeFixed H) ≫ stripSquare α =
      α ≫ comparisonPaste O M (includeFixed F) (compose O (includeFixed G) (includeFixed H)) :=
  paste_natural O M laws _ _ _ _ α

def fixedFrame (X : Type u) (F : Fixed P I A B) : Fixed P I (X × A) (X × B) :=
  ⟨fun x => F.ctx x.2,fun x w => ⟨(F.body x.2 w).arity,PUnit.unit,fun i => (x.1,(F.body x.2 w).label i)⟩⟩

theorem frame_strip (X : Type u) (F : Operation P I A B) : strip (frameOp X F) = fixedFrame X (strip F) := rfl
theorem frame_include (X : Type u) (F : Fixed P I A B) : frameOp X (includeFixed F) = includeFixed (fixedFrame X F) := rfl

theorem frame_comparison (X : Type u) (F : Fixed P I A B) (G : Fixed P I B C) :
    frameSquare X (multiplication O F G) = multiplication O (fixedFrame X F) (fixedFrame X G) := rfl

end ContextualComposition.OrderedArityAssembly
