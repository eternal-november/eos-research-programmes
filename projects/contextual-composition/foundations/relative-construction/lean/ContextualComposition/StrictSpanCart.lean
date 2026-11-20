module
public import ContextualComposition.StrictSpanAlgebra
public import ContextualComposition.ContextadCartesian
@[expose] public section
namespace ContextualComposition.GrothendieckStep.StrictSpanCart
open CategoryTheory SpanApex NativeBlocks NativeCleavage
open Limits
open NativeBlocks.Nested (Over)
open StrictSpanAlgebra
universe b w x y
set_option backward.isDefEq.respectTransparency false
variable {B : Type b} [Category.{max b w} B]

section Factor
variable {X : Type x} [Category.{y} X] {p : X ⥤ B} {a b z : X} {f : a ⟶ b}

theorem cancelCart (hf : Cartesian p f) {i j : z ⟶ a}
    (h : p.map i = p.map j) (eq : i ≫ f = j ≫ f) : i = j := by
  obtain ⟨k,_,uk⟩ := hf z (j ≫ f) (p.map j) (p.map_comp j f)
  exact (uk i ⟨h,eq⟩).trans (uk j ⟨rfl,rfl⟩).symm

/-- Compare an arbitrary cartesian arrow with the chosen lift; no choice
is required to be fixed by a strict cartesian map. -/
theorem compareChosen (hf : Cartesian p f)
    (c : Choice p (p.obj a) b (p.map f)) :
    ∃ i : a ≅ c.obj, i.hom ≫ c.lift = f := by
  obtain ⟨i,⟨io,ifac⟩,_⟩ := c.cart a f (eqToHom c.source.symm) (by rw [c.over]; simp)
  obtain ⟨j,⟨jo,jfac⟩,_⟩ := hf c.obj c.lift (eqToHom c.source) c.over
  refine ⟨⟨i,j,?_,?_⟩,ifac⟩
  · apply cancelCart hf
    · rw [p.map_comp,io,jo,Functor.map_id]; simp
    · rw [Category.assoc,jfac,ifac,Category.id_comp]
  · apply cancelCart c.cart
    · rw [p.map_comp,io,jo,Functor.map_id]; simp
    · rw [Category.assoc,ifac,jfac,Category.id_comp]
end Factor

variable {U V W T : Span (B := B)}
theorem identity (U : Span (B := B)) : CartesianMap (StrictSpanAlgebra.id U) :=
  fun _ h => h
theorem compose {F : Over U V} {G : Over V W}
    (f : CartesianMap F) (g : CartesianMap G) :
    CartesianMap (StrictSpanAlgebra.comp F G) := fun k h => g _ (f k h)
theorem isomorphism (F : Over U V) [F.functor.IsIso] : CartesianMap F := by
  have h := BlockCartesian.isoIncoming F.functor
  intro x y k hk
  exact (BlockCartesian.cartesian_iff F.functor h V.source k).mp (F.source ▸ hk)

theorem pairOf {x y : (Pair U V).apex} (f : x ⟶ y)
    (h₁ : Cartesian U.source f.hom.fst) (h₂ : Cartesian V.source f.hom.snd) :
    Cartesian (Pair U V).source f :=
  NativeCleavage.composite (BlockCartesian.fstCartesian _ _ _ h₂) h₁

theorem pairTo (c : Cleavage U.source) (d : Cleavage V.source)
    {x y : (Pair U V).apex} (f : x ⟶ y) (h : Cartesian (Pair U V).source f) :
    Cartesian U.source f.hom.fst ∧ Cartesian V.source f.hom.snd := by
  let ch := BlockCartesian.productChoice U.dest V.source U.source c d _ y ((Pair U V).source.map f)
  obtain ⟨i,eq⟩ := compareChosen h ch
  have e₁ := congrArg (fun k : x ⟶ y => k.hom.fst) eq
  have e₂ := congrArg (fun k : x ⟶ y => k.hom.snd) eq
  let i₁ := (Strict.fst U.dest V.source).mapIso i
  let i₂ := (Strict.snd U.dest V.source).mapIso i
  constructor
  · rw [← e₁]
    exact pasteCart (ContextadCartesian.vertical_cart (p := U.source) i₁.hom)
      (BlockCartesian.prefixLift U.dest V.source U.source c _ y ((Pair U V).source.map f)).cart
  · rw [← e₂]
    exact pasteCart (ContextadCartesian.vertical_cart (p := V.source) i₂.hom)
      (BlockCartesian.suffixLift U.dest V.source U.source c d _ y ((Pair U V).source.map f)).cart

theorem bothCart (c : Cleavage U.source) (d : Cleavage V.source)
    {F : Over U W} {G : Over V T} (f : CartesianMap F) (g : CartesianMap G) :
    CartesianMap (both F G) := by
  intro x y k hk
  have e := pairTo c d k hk
  exact pairOf ((both F G).functor.map k) (f _ e.1) (g _ e.2)

end ContextualComposition.GrothendieckStep.StrictSpanCart
