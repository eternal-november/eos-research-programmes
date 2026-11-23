module
public import ContextualComposition.OrderedNativeFraming
public import ContextualComposition.NativeOrderedFubini

/-! The constant-collection framing comparisons on the actual ordered
native independent product and dependent Fubini implementation. -/

@[expose] public section
namespace ContextualComposition.OrderedRigFraming
open CategoryTheory MonoidalCategory NativeFinitePush NativeFinitePush.DependentFibre
open RigGrid NativeFinitePush.DependentFibre.RigGridNativeAdapter
open OrderedArityReflection ConstantCollectionFraming OrderedNativeFraming
open scoped MonoidalCategory
universe u v
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
local notation "ℙ" => standardPush (C := C)
variable {T : Bi (coeff (C:=C))} {I : C}
variable (R : Gather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (L : LeftGather (binary (Additive.ofBraided (C:=C)).sum) T (𝟙_ C))
variable (c : T.obj I I ⟶ I)
variable (N : GridBinary (symmetricCross (C:=C)) R L) (NR : GatherOuterNat R) (NL : GatherLeftNat L)
variable [lF : ∀ a : C, (leftFactor T a).LaxBraided] [rF : ∀ b : C, (rightFactor (T:=T) b).LaxBraided]
variable (hl : ∀ a : C, SameLeftGather T a L) (hr : ∀ b : C, SameRightGather R b)

/-- The separate dependent-serial operation of an admitted context
presentation. The occurrence operation and its maps below are constructed
by the pinned ordered native product. -/
structure DependentOperations (I : C) where
  obj : (a : Aug ℙ I) → (Pos a → Aug ℙ I) → Aug ℙ I
  positions : ∀ a b, Pos (obj a b) ≃ Σ x : Pos a, Pos (b x)
  map : ∀ {a a' : Aug ℙ I} {b : Pos a → Aug ℙ I} {b' : Pos a' → Aug ℙ I} (f : AugHom ℙ a a'),
    (∀ x, AugHom ℙ (b x) (b' (f.native.addr x))) → AugHom ℙ (obj a b) (obj a' b')
  read_map : ∀ {a a' : Aug ℙ I} {b : Pos a → Aug ℙ I} {b' : Pos a' → Aug ℙ I} (f : AugHom ℙ a a')
    (g : ∀ x, AugHom ℙ (b x) (b' (f.native.addr x))) w, positions a' b' ((map f g).native.addr w) =
      (let z := positions a b w; ⟨f.native.addr z.1,(g z.1).native.addr z.2⟩)

variable (D : DependentOperations I)

noncomputable def operations : ContextOps ℙ I where
  occurrence := independentAugFold R L c
  occurrencePos := independentAugFoldPositions R L c
  occurrenceMap := independentAugFoldMap R L c N NR NL hl hr
  dependent := D.obj
  dependentPos := D.positions

noncomputable def maps : MapOps (operations R L c N NR NL hl hr D) where
  occurrence_read := independentAugFoldRead_addr R L c N NR NL hl hr
  dependentMap := D.map
  dependent_read := D.read_map

variable {G : Collection.{u}} {B X : Type u}

/-- The coefficient on a framed occurrence witness is the ordered
tensor of the original coefficients at its exact readout addresses. -/
theorem framed_coefficient (q : B → Aug ℙ I) (x : X) (z : Point G B)
    (w : Pos (occurrenceAt (operations R L c N NR NL hl hr D) q z)) :
    (let z' := (CanonicalSetStrength.strength (extF G) X).app B (x,z)
     (independentAugFold R L c z'.arity (fun i => q (z'.label i).2)).base.val w) =
      independentAugCoefficient T I z.arity (fun i => (q (z.label i)).base.val
        (independentAugFoldRead R L c z.arity (fun i => q (z.label i)) w i)) :=
  independentAugFold_label R L c z.arity _ w

omit lF rF in
theorem unary_occurrence (q : Aug ℙ I) : independentAugFold R L c 1 (fun _ => q) = q := rfl
omit lF rF in
theorem nullary_occurrence (q : Fin 0 → Aug ℙ I) : independentAugFold R L c 0 q = AugHom.unit I := rfl

variable (J : UnitCompat R I)
variable (m : Middle T I) (mi : MiddleInv m) (h : MedialLinear m R L) (j : MedialInner m R L)
variable (unit_middle : m.cell I I I I ≫ unitCollapse R J = unitCollapse R J) [IsIso (J.ρ I)]

/-- The context-accumulation modification is the already-constructed
augmented Fubini isomorphism on both framed and original occurrences. -/
theorem context_accumulation (p : B → OrderedDependentAugData I) (x : X) (z : Point G B) :
    (let z' := (CanonicalSetStrength.strength (extF G) X).app B (x,z)
     orderedFubini R L N NR NL hl hr J m mi h j unit_middle z'.arity (fun i => p (z'.label i).2)) =
      orderedFubini R L N NR NL hl hr J m mi h j unit_middle z.arity (fun i => p (z.label i)) := rfl

/-- Naturality is equality of composites of actual augmented morphisms,
retaining empty preimages and every coefficient map. -/
theorem context_accumulation_natural {a b : B → OrderedDependentAugData I}
    (k : ∀ t, OrderedDependentAugArrow (a t) (b t)) (x : X) (z : Point G B) :
    (let z' := (CanonicalSetStrength.strength (extF G) X).app B (x,z)
     (independentAugFoldMap R L (J.ρ I) N NR NL hl hr z'.arity (fun i => (k (z'.label i).2).accumulate R L J N NL hl)).comp
       (orderedFubini R L N NR NL hl hr J m mi h j unit_middle z'.arity (fun i => b (z'.label i).2)).hom) =
      (orderedFubini R L N NR NL hl hr J m mi h j unit_middle z.arity (fun i => a (z.label i))).hom.comp
        ((dependentInputFoldMap R L N NR NL hl hr J z.arity (fun i => k (z.label i))).accumulate R L J N NL hl) :=
  orderedFubini_natural R L N NR NL hl hr J m mi h j unit_middle z.arity (fun i => k (z.label i))

end ContextualComposition.OrderedRigFraming
