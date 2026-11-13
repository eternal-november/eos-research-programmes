module

public import WitnessedDecompositions.FreeExtension
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

universe u v w w' w'' z z'

namespace WitnessedDecompositions

namespace Collection
variable {V : Type u} [Quiver.{v} V]

/-- Totalized primitive generators of an arbitrary profiled collection. -/
def signature (C : Collection.{u, v, w} V) : Signature.{u, v, max u v w} V where
  Generator := (c : Component V) × C.Op c
  source g := g.1.source
  target g := g.1.target
  input g := C.profile g.2
  output g := g.1.edge

@[simp] theorem signature_result (C : Collection.{u, v, w} V)
    (c : Component V) (a : C.Op c) : C.signature.result ⟨c, a⟩ = c := rfl

end Collection

namespace Signature
variable {V : Type u} [Quiver.{v} V]

/-- Regroup exactly the original raw generators by their output component.
The equality proof transports the full input path, never just its length. -/
def generatingCollection (S : Signature.{u, v, w} V) : Collection.{u, v, w} V where
  Op c := {g : S.Generator // S.result g = c}
  profile a := Component.transport
    (F := fun c => Quiver.Path c.source c.target) a.property (S.input a.val)

/-- Totalizing the output fibres recovers exactly the original generator type. -/
def totalizedGeneratorEquiv (S : Signature.{u, v, w} V) :
    S.Generator ≃ S.generatingCollection.signature.Generator where
  toFun g := ⟨S.result g, ⟨g, rfl⟩⟩
  invFun a := a.2.val
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨c, g, h⟩
    cases h
    rfl

@[simp] theorem totalizedGeneratorEquiv_result (S : Signature.{u, v, w} V)
    (g : S.Generator) :
    S.generatingCollection.signature.result (S.totalizedGeneratorEquiv g) = S.result g := rfl

@[simp] theorem totalizedGeneratorEquiv_input (S : Signature.{u, v, w} V)
    (g : S.Generator) :
    S.generatingCollection.signature.input (S.totalizedGeneratorEquiv g) = S.input g := rfl

/-- The backwards generator bijection preserves the output after the recorded equality. -/
theorem totalizedGeneratorEquiv_symm_result (S : Signature.{u, v, w} V)
    (a : S.generatingCollection.signature.Generator) :
    S.result (S.totalizedGeneratorEquiv.symm a) =
      S.generatingCollection.signature.result a := a.2.property

/-- Its backwards profile transport is exactly that defining the generating collection. -/
theorem totalizedGeneratorEquiv_symm_input (S : Signature.{u, v, w} V)
    (a : S.generatingCollection.signature.Generator) :
    Component.transport (F := fun c => Quiver.Path c.source c.target)
      (S.totalizedGeneratorEquiv_symm_result a)
      (S.input (S.totalizedGeneratorEquiv.symm a)) =
      S.generatingCollection.signature.input a := rfl

/-- The original raw assignments and generating-collection maps coincide,
for every target calculus in an independently chosen operation universe. -/
def assignmentCollectionEquiv (S : Signature.{u, v, w} V)
    (M : Calc.{u, v, z} V) :
    S.Assignment M ≃ Collection.Hom S.generatingCollection M.toCollection where
  toFun a :=
    { map := fun x => Component.transport x.property (a x.val).val
      profile_map := by
        intro c x
        rcases x with ⟨g, h⟩
        cases h
        exact (a g).property }
  invFun f := fun g => ⟨f.map ⟨g, rfl⟩, f.profile_map ⟨g, rfl⟩⟩
  left_inv a := by
    funext g
    rfl
  right_inv f := by
    apply Collection.Hom.ext
    intro c x
    rcases x with ⟨g, h⟩
    cases h
    rfl

/-- Raw-signature maps are maps of typed generator fibres. This is equivalent
to ordinary generator functions preserving output and the transported whole profile. -/
abbrev Hom (S : Signature.{u, v, w} V) (T : Signature.{u, v, w'} V) :=
  Collection.Hom S.generatingCollection T.generatingCollection

namespace Hom
variable {S : Signature.{u, v, w} V} {T : Signature.{u, v, w'} V}

/-- The ordinary raw generator function underlying a typed-fibre map. -/
def generatorMap (f : Hom S T) (g : S.Generator) : T.Generator :=
  (f.map ⟨g, rfl⟩).val

/-- Raw generator maps preserve the complete output component. -/
theorem result_map (f : Hom S T) (g : S.Generator) :
    T.result (generatorMap f g) = S.result g := (f.map ⟨g, rfl⟩).property

/-- Raw generator maps preserve the full input path after the required output transport. -/
theorem input_map (f : Hom S T) (g : S.Generator) :
    Component.transport (F := fun c => Quiver.Path c.source c.target)
      (result_map f g) (T.input (generatorMap f g)) = S.input g :=
  f.profile_map ⟨g, rfl⟩

/-- Conversely, exactly the ordinary boundary-preserving generator functions define maps. -/
def ofGeneratorMap (f : S.Generator → T.Generator)
    (hr : ∀ g, T.result (f g) = S.result g)
    (hp : ∀ g, Component.transport (F := fun c => Quiver.Path c.source c.target)
      (hr g) (T.input (f g)) = S.input g) : Hom S T where
  map x := ⟨f x.val, (hr x.val).trans x.property⟩
  profile_map := by
    intro c x
    rcases x with ⟨g, h⟩
    cases h
    exact hp g

@[simp] theorem generatorMap_ofGeneratorMap (f : S.Generator → T.Generator)
    (hr : ∀ g, T.result (f g) = S.result g)
    (hp : ∀ g, Component.transport (F := fun c => Quiver.Path c.source c.target)
      (hr g) (T.input (f g)) = S.input g) :
    generatorMap (ofGeneratorMap f hr hp) = f := rfl

@[simp] theorem ofGeneratorMap_generatorMap (f : Hom S T) :
    ofGeneratorMap (generatorMap f) (result_map f) (input_map f) = f := by
  apply Collection.Hom.ext
  intro c x
  rcases x with ⟨g, h⟩
  cases h
  rfl

end Hom

/-- The original raw signatures form a category, with exactly the boundary-preserving maps. -/
instance : CategoryTheory.Category (Signature.{u, v, w} V) where
  Hom := Hom
  id S := Collection.Hom.id S.generatingCollection
  comp := Collection.Hom.comp

end Signature

namespace Collection
variable {V : Type u} [Quiver.{v} V]

/-- Embed a collection into the output fibres of its totalized raw signature. -/
def toSignatureCollection (C : Collection.{u, v, w} V) :
    Hom C C.signature.generatingCollection where
  map := fun {c} a => ⟨⟨c, a⟩, rfl⟩
  profile_map _ := rfl

/-- Recover the original operation, transporting along its retained output equality. -/
def fromSignatureCollection (C : Collection.{u, v, w} V) :
    Hom C.signature.generatingCollection C where
  map a := Component.transport a.property a.val.2
  profile_map := by
    intro c a
    rcases a with ⟨⟨d, a⟩, h⟩
    cases h
    rfl

@[simp] theorem to_from_signatureCollection (C : Collection.{u, v, w} V) :
    C.toSignatureCollection.comp C.fromSignatureCollection = Hom.id C := by
  apply Hom.ext
  intros
  rfl

@[simp] theorem from_to_signatureCollection (C : Collection.{u, v, w} V) :
    C.fromSignatureCollection.comp C.toSignatureCollection =
      Hom.id C.signature.generatingCollection := by
  apply Hom.ext
  intro c a
  rcases a with ⟨⟨d, a⟩, h⟩
  cases h
  rfl

end Collection

namespace Free
variable {V : Type u} [Quiver.{v} V]

/-- The free calculus on arbitrary profiled generators. -/
def obj (C : Collection.{u, v, w} V) : Calc.{u, v, max u v w} V :=
  Tree.freeCalc C.signature

/-- A collection morphism is exactly an assignment to the totalized primitives. -/
def assignmentEquiv (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V) :
    C.signature.Assignment M ≃ Collection.Hom C M.toCollection where
  toFun a :=
    { map := fun {c} x => (a ⟨c, x⟩).val
      profile_map := fun x => (a ⟨_, x⟩).property }
  invFun f := fun g => ⟨f.map g.2, f.profile_map g.2⟩
  left_inv a := by
    funext g
    rfl
  right_inv f := by
    apply Collection.Hom.ext
    intros
    rfl

/-- Restrict every strict map to the primitive corollas. -/
def restrict (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V)
    (f : Calc.Hom (obj C) M) : Collection.Hom C M.toCollection :=
  assignmentEquiv C M (Tree.restrict M f)

/-- Extend a profile-preserving primitive assignment; leaves are identities. -/
def extend (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V)
    (a : Collection.Hom C M.toCollection) : Calc.Hom (obj C) M :=
  Tree.extend M ((assignmentEquiv C M).symm a)

/-- The unrestricted free hom-set equivalence, with independent operation universes. -/
def homEquiv (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V) :
    Calc.Hom (obj C) M ≃ Collection.Hom C M.toCollection :=
  (Tree.homEquiv M).trans (assignmentEquiv C M)

@[simp] theorem restrict_extend (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V)
    (a : Collection.Hom C M.toCollection) : restrict C M (extend C M a) = a :=
  (homEquiv C M).apply_symm_apply a

@[simp] theorem extend_restrict (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V)
    (f : Calc.Hom (obj C) M) : extend C M (restrict C M f) = f :=
  (homEquiv C M).symm_apply_apply f

/-- Uniqueness ranges over all strict calculus morphisms, not recursive maps. -/
theorem extend_unique (C : Collection.{u, v, w} V) (M : Calc.{u, v, z} V)
    (a : Collection.Hom C M.toCollection) (f : Calc.Hom (obj C) M)
    (h : restrict C M f = a) : f = extend C M a := by
  apply (homEquiv C M).injective
  exact h.trans (restrict_extend C M a).symm

/-- The unit sends a primitive to its one-vertex corolla, not to an identity. -/
def unit (C : Collection.{u, v, w} V) : Collection.Hom C (obj C).toCollection where
  map := fun {c} a => Tree.corolla (S := C.signature) ⟨c, a⟩
  profile_map := fun a => Tree.frontier_corolla (S := C.signature) ⟨_, a⟩

@[simp] theorem restrict_eq_unit_comp (C : Collection.{u, v, w} V)
    (M : Calc.{u, v, z} V) (f : Calc.Hom (obj C) M) :
    restrict C M f = (unit C).comp f.toHom := rfl

/-- Restriction is covariantly natural in every target strict morphism. -/
theorem restrict_comp (C : Collection.{u, v, w} V)
    {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (f : Calc.Hom (obj C) M) (k : Calc.Hom M N) :
    restrict C N (f.comp k) = (restrict C M f).comp k.toHom := rfl

/-- Free action on an arbitrary generator map. -/
def map {C : Collection.{u, v, w} V} {D : Collection.{u, v, w'} V}
    (s : Collection.Hom C D) : Calc.Hom (obj C) (obj D) :=
  extend C (obj D) (s.comp (unit D))

@[simp] theorem restrict_map {C : Collection.{u, v, w} V}
    {D : Collection.{u, v, w'} V} (s : Collection.Hom C D) :
    restrict C (obj D) (map s) = s.comp (unit D) :=
  restrict_extend C (obj D) _

/-- Naturality of restriction in the signature variable, including universe changes. -/
theorem restrict_natural_source {C : Collection.{u, v, w} V}
    {D : Collection.{u, v, w'} V} {M : Calc.{u, v, z} V}
    (s : Collection.Hom C D) (f : Calc.Hom (obj D) M) :
    restrict C M ((map s).comp f) = s.comp (restrict D M f) := by
  rw [restrict_comp, restrict_map]
  rfl

/-- Extension is natural under arbitrary changes of target calculus. -/
theorem extend_natural_target (C : Collection.{u, v, w} V)
    {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (a : Collection.Hom C M.toCollection) (k : Calc.Hom M N) :
    (extend C M a).comp k = extend C N (a.comp k.toHom) := by
  apply extend_unique
  rw [restrict_comp, restrict_extend]

/-- Extension is contravariantly natural in the generating collection. -/
theorem extend_natural_source {C : Collection.{u, v, w} V}
    {D : Collection.{u, v, w'} V} {M : Calc.{u, v, z} V}
    (s : Collection.Hom C D) (a : Collection.Hom D M.toCollection) :
    (map s).comp (extend D M a) = extend C M (s.comp a) := by
  apply extend_unique
  rw [restrict_natural_source, restrict_extend]

/-- The two-variable naturality square at fully independent operation universes. -/
theorem extend_natural {C : Collection.{u, v, w} V}
    {D : Collection.{u, v, w'} V} {M : Calc.{u, v, z} V}
    {N : Calc.{u, v, z'} V} (s : Collection.Hom C D)
    (a : Collection.Hom D M.toCollection) (k : Calc.Hom M N) :
    ((map s).comp (extend D M a)).comp k =
      extend C N ((s.comp a).comp k.toHom) := by
  rw [extend_natural_source, extend_natural_target]

@[simp] theorem map_id (C : Collection.{u, v, w} V) :
    map (Collection.Hom.id C) = Calc.Hom.id (obj C) := by
  symm
  apply extend_unique
  rfl

theorem map_comp {C : Collection.{u, v, w} V}
    {D : Collection.{u, v, w'} V} {E : Collection.{u, v, w''} V}
    (s : Collection.Hom C D) (t : Collection.Hom D E) :
    map (s.comp t) = (map s).comp (map t) := by
  symm
  apply extend_unique
  rw [restrict_natural_source, restrict_map]
  rfl

/-- The counit evaluates primitives named by actual target operations. -/
def counit (M : Calc.{u, v, z} V) : Calc.Hom (obj M.toCollection) M :=
  extend M.toCollection M (Collection.Hom.id M.toCollection)

/-- The generator inclusion is a natural transformation. -/
theorem unit_natural {C : Collection.{u, v, w} V}
    {D : Collection.{u, v, w'} V} (s : Collection.Hom C D) :
    (unit C).comp (map s).toHom = s.comp (unit D) := restrict_map s

/-- Evaluation is a natural transformation. -/
theorem counit_natural {M : Calc.{u, v, z} V} {N : Calc.{u, v, z'} V}
    (k : Calc.Hom M N) :
    (map k.toHom).comp (counit N) = (counit M).comp k := by
  rw [counit, extend_natural_source, counit, extend_natural_target]
  rfl

/-- The first triangular identity, as equality of strict morphisms. -/
theorem triangle_free (C : Collection.{u, v, w} V) :
    (map (unit C)).comp (counit (obj C)) = Calc.Hom.id (obj C) := by
  rw [counit, extend_natural_source]
  symm
  apply extend_unique
  rfl

/-- The second triangular identity, as equality of generator maps. -/
theorem triangle_forget (M : Calc.{u, v, z} V) :
    (unit M.toCollection).comp (counit M).toHom = Collection.Hom.id M.toCollection :=
  restrict_extend M.toCollection M _

/-- A raw signature embeds into its actual original tree calculus. -/
def rawUnit (S : Signature.{u, v, w} V) :
    Collection.Hom S.generatingCollection (Tree.freeCalc S).toCollection :=
  S.assignmentCollectionEquiv (Tree.freeCalc S) (fun g => Tree.generatorOperation g)

/-- The explicit strict comparison from the original frozen free calculus. -/
def rawToProfiled (S : Signature.{u, v, w} V) :
    Calc.Hom (Tree.freeCalc S) (obj S.generatingCollection) :=
  Tree.extend (obj S.generatingCollection)
    (fun g => Tree.generatorOperation (S.totalizedGeneratorEquiv g))

/-- The reverse comparison evaluates the regrouped primitives as the original corollas. -/
def profiledToRaw (S : Signature.{u, v, w} V) :
    Calc.Hom (obj S.generatingCollection) (Tree.freeCalc S) :=
  extend S.generatingCollection (Tree.freeCalc S) (rawUnit S)

@[simp] theorem rawToProfiled_profiledToRaw (S : Signature.{u, v, w} V) :
    (rawToProfiled S).comp (profiledToRaw S) = Calc.Hom.id (Tree.freeCalc S) := by
  apply (Tree.homEquiv (Tree.freeCalc S)).injective
  change Tree.restrict _ _ = Tree.restrict _ _
  rw [Tree.restrict_comp]
  unfold rawToProfiled
  rw [Tree.restrict_extend]
  funext g
  apply Subtype.ext
  exact Tree.interpret_corolla _ _ _

@[simp] theorem profiledToRaw_rawToProfiled (S : Signature.{u, v, w} V) :
    (profiledToRaw S).comp (rawToProfiled S) = Calc.Hom.id (obj S.generatingCollection) := by
  apply (homEquiv S.generatingCollection (obj S.generatingCollection)).injective
  change restrict _ _ _ = restrict _ _ _
  rw [restrict_comp]
  unfold profiledToRaw
  rw [restrict_extend]
  apply Collection.Hom.ext
  intro c a
  rcases a with ⟨g, h⟩
  cases h
  exact Tree.interpret_corolla _ _ _

/-- Forget only identity and substitution structure; preserve every operation/profile. -/
def forgetFunctor (V : Type u) [Quiver.{v} V] :
    CategoryTheory.Functor (Calc.{u, v, max u v w} V)
      (Collection.{u, v, max u v w} V) where
  obj M := M.toCollection
  map k := k.toHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An actual free functor at any common universe containing the fixed base. -/
def functor (V : Type u) [Quiver.{v} V] :
    CategoryTheory.Functor (Collection.{u, v, max u v w} V)
      (Calc.{u, v, max u v w} V) where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The free-forgetful adjunction. The cross-universe hom theorem above is stronger
than this necessarily fixed-universe categorical packaging. -/
def adjunction (V : Type u) [Quiver.{v} V] :
    CategoryTheory.Adjunction (functor.{u, v, w} V) (forgetFunctor.{u, v, w} V) where
  unit := { app := unit, naturality := fun _ _ s => (unit_natural s).symm }
  counit := { app := counit, naturality := fun _ _ k => counit_natural k }
  left_triangle_components := triangle_free
  right_triangle_components := triangle_forget

/-- The packaged adjunction induces exactly the explicit restriction map. -/
@[simp] theorem adjunction_homEquiv_apply (V : Type u) [Quiver.{v} V]
    (C : Collection.{u, v, max u v w} V) (M : Calc.{u, v, max u v w} V)
    (f : Calc.Hom (obj C) M) :
    (adjunction.{u, v, w} V).homEquiv C M f = homEquiv C M f := rfl

/-- The packaged adjunction's inverse is exactly extension, not merely some inverse. -/
@[simp] theorem adjunction_homEquiv_symm_apply (V : Type u) [Quiver.{v} V]
    (C : Collection.{u, v, max u v w} V) (M : Calc.{u, v, max u v w} V)
    (a : Collection.Hom C M.toCollection) :
    ((adjunction.{u, v, w} V).homEquiv C M).symm a = (homEquiv C M).symm a := by
  change (map a).comp (counit M) = extend C M a
  rw [counit, extend_natural_source, Collection.Hom.comp_id]

end Free
end WitnessedDecompositions
