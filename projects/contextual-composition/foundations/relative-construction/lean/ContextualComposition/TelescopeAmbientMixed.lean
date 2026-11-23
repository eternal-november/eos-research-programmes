module
public import ContextualComposition.TelescopeAmbientBase
public import ContextualComposition.TelescopeAmbientComponents
public import ContextualComposition.MixedMates

@[expose] public section
namespace ContextualComposition.GrothendieckStep.TelescopeAmbientMixed
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open CoproductSpan CoproductSpan.All SumChange SpanPull.All ContextadAmbientPayload
open AmbientBicategory TelescopeAmbientComponents FinalCube TaggedMixed
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
set_option backward.isDefEq.respectTransparency false
universe u v
variable {B : Type u} [Category.{max u v} B] {P : Endpoints.{u,max u v,u,max u v} B}
variable (S : P.Split) {X Y : Obj.{u,v} B} (f : X ⟶ Y) {A D : B} (a : A ⟶ D)

noncomputable abbrev weighted (A : B) (n : Nat) := atEndpoint f.hom (leg (src S) (dst S) A n)
noncomputable def nativeLeaf : (n : Nat) →
    leafPull S (underlying X) a n ⋙ weighted S f A n ≅ weighted S f D n ⋙ leafPull S (underlying Y) a n
  | 0 => TelescopeAmbientBase.presented f.hom (dst S 0) (src S 0) (parts S 0) a
  | n+1 => TelescopeAmbientBase.presented f.hom (dst S (n+1)) (src S (n+1)) (parts S (n+1)) a

/-- The reindexing cell of the independent ambient iterate action, before taking the sum of lengths. -/
noncomputable def iterateLeaf (n : Nat) :
    ((Iterates.layer P S (underlying X) n).map a.op).toFunctor ⋙ target S A f n ≅
      target S D f n ⋙ ((Iterates.layer P S (underlying Y) n).map a.op).toFunctor :=
  Cat.Hom.toNatIso ((AmbientBicategory.map S n f).hom.naturality a.op.toLoc)

noncomputable def sourceLeaf (n : Nat) : Mix.Grid where
  A := Total (underlying X) (leg (src S) (dst S) A n)
  D := Total (underlying X) (leg (src S) (dst S) D n)
  A' := Total (underlying Y) (leg (src S) (dst S) A n)
  D' := Total (underlying Y) (leg (src S) (dst S) D n)
  b := leafPull S (underlying X) a n
  b' := leafPull S (underlying Y) a n
  p := weighted S f A n
  q := weighted S f D n
  cell := (nativeLeaf S f a n).hom

noncomputable def targetLeaf (n : Nat) : Mix.Grid where
  A := (Iterates.layer P S (underlying X) n).obj (op A)
  D := (Iterates.layer P S (underlying X) n).obj (op D)
  A' := (Iterates.layer P S (underlying Y) n).obj (op A)
  D' := (Iterates.layer P S (underlying Y) n).obj (op D)
  b := ((Iterates.layer P S (underlying X) n).map a.op).toFunctor
  b' := ((Iterates.layer P S (underlying Y) n).map a.op).toFunctor
  p := target S A f n
  q := target S D f n
  cell := (iterateLeaf S f a n).hom

noncomputable def leafMap (n : Nat) : Cube.Map (sourceLeaf S f a n) (targetLeaf S f a n) where
  f := (component S (underlying X) A n).functor
  g := (component S (underlying X) D n).functor
  f' := (component S (underlying Y) A n).functor
  g' := (component S (underlying Y) D n).functor
  s := (componentBase S (underlying X) a n).hom
  t := (componentBase S (underlying Y) a n).hom
  l := (eqToIso (component_payload S A f n)).inv
  r := (eqToIso (component_payload S D f n)).inv

noncomputable def taggedGrid : Mix.Grid where
  A := Σ n, Total (underlying X) (leg (src S) (dst S) A n)
  D := Σ n, Total (underlying X) (leg (src S) (dst S) D n)
  A' := Σ n, Total (underlying Y) (leg (src S) (dst S) A n)
  D' := Σ n, Total (underlying Y) (leg (src S) (dst S) D n)
  b := ZeroPower.Sum.map (leafPull S (underlying X) a)
  b' := ZeroPower.Sum.map (leafPull S (underlying Y) a)
  p := ZeroPower.Sum.map (weighted S f A)
  q := ZeroPower.Sum.map (weighted S f D)
  cell := (Tagged.square _ _ _ _ (nativeLeaf S f a)).hom

noncomputable def wholeGrid : Mix.Grid where
  A := Total (underlying X) (wholeLeg (src S) (dst S) A)
  D := Total (underlying X) (wholeLeg (src S) (dst S) D)
  A' := Total (underlying Y) (wholeLeg (src S) (dst S) A)
  D' := Total (underlying Y) (wholeLeg (src S) (dst S) D)
  b := pull S (underlying X) a
  b' := pull S (underlying Y) a
  p := atEndpoint f.hom (wholeLeg (src S) (dst S) A)
  q := atEndpoint f.hom (wholeLeg (src S) (dst S) D)
  cell := (TelescopeAmbientBase.whole f.hom a S).hom

noncomputable def packedGrid : Mix.Grid where
  A := Iterates.Packed P S (underlying X) (op A)
  D := Iterates.Packed P S (underlying X) (op D)
  A' := Iterates.Packed P S (underlying Y) (op A)
  D' := Iterates.Packed P S (underlying Y) (op D)
  b := Iterates.packedMap P S (underlying X) a.op
  b' := Iterates.packedMap P S (underlying Y) a.op
  p := ZeroPower.Sum.map (target S A f)
  q := ZeroPower.Sum.map (target S D f)
  cell := (Tagged.square _ _ _ _ (iterateLeaf S f a)).hom

noncomputable def presentation : MixedMates.Frame (taggedGrid S f a) (wholeGrid S f a) where
  f := (compare (src S) (dst S) A (underlying X)).asEquivalence
  g := (compare (src S) (dst S) D (underlying X)).asEquivalence
  f' := (compare (src S) (dst S) A (underlying Y)).asEquivalence
  g' := (compare (src S) (dst S) D (underlying Y)).asEquivalence
  s := comparison S (underlying X) a
  t := comparison S (underlying Y) a
  l := eqToIso (TelescopeGradeChange.compare_payload f.hom (src S) (dst S) A)
  r := eqToIso (TelescopeGradeChange.compare_payload f.hom (src S) (dst S) D)

noncomputable def tagged : MixedMates.Frame (taggedGrid S f a) (packedGrid S f a) where
  f := ZeroPower.Sum.equiv (component S (underlying X) A)
  g := ZeroPower.Sum.equiv (component S (underlying X) D)
  f' := ZeroPower.Sum.equiv (component S (underlying Y) A)
  g' := ZeroPower.Sum.equiv (component S (underlying Y) D)
  s := (taggedBase S (underlying X) a).symm
  t := (taggedBase S (underlying Y) a).symm
  l := Tagged.square _ _ _ _ (fun n => eqToIso (component_payload S A f n))
  r := Tagged.square _ _ _ _ (fun n => eqToIso (component_payload S D f n))

theorem tagged_of_lengths (h : ∀ n, Cube.Law (leafMap S f a n)) : Cube.Law (tagged S f a).forward := by
  rintro ⟨n,x⟩
  exact congrArg Sigma.SigmaHom.mk (h n x)

/-- All four sides are the original base comparison and the assembled strong-payload comparisons. -/
noncomputable def evaluationCube : Cube.Map (wholeGrid S f a) (packedGrid S f a) :=
  ((presentation S f a).reverse.compose (tagged S f a)).forward

theorem source_base_face : (evaluationCube S f a).s = (evaluationBase S (underlying X) a).hom := rfl
theorem target_base_face : (evaluationCube S f a).t = (evaluationBase S (underlying Y) a).hom := rfl
theorem source_payload_face : (evaluationCube S f a).l = (evaluation_payload S A f).inv := rfl
theorem target_payload_face : (evaluationCube S f a).r = (evaluation_payload S D f).inv := rfl

/-- The presentation face and the independently established lengthwise laws give equality of the two final mixed pastes. -/
theorem evaluation_of_faces (presentationLaw : Cube.Law (presentation S f a).forward)
    (lengthLaw : ∀ n, Cube.Law (leafMap S f a n)) : ForwardMixed.Commuting (evaluationCube S f a) :=
  ForwardMixed.commuting _ ((presentation S f a).reverse.composeLaw (tagged S f a)
    ((presentation S f a).backLaw presentationLaw) (tagged_of_lengths S f a lengthLaw))

end ContextualComposition.GrothendieckStep.TelescopeAmbientMixed
